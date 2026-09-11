import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFortyEightEPFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFortyEightEPFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFortyEightEPFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFortyEightEPFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFortyEightEPFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFortyEightEPFastPow a n * oneHundredFortyEightEPFastPow a n * a else oneHundredFortyEightEPFastPow a n * oneHundredFortyEightEPFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFortyEightEP_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFortyEightEP_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFortyEightEP_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFortyEightEP_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFortyEightEP_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFortyEightEP_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFortyEightEP_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFortyEightEP_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFortyEightEP_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFortyEightEP_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFortyEightEP_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFortyEightEP_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFortyEightEP_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFortyEightEP_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFortyEightEP_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFortyEightEP_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFortyEightEP_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFortyEightEP_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFortyEightEP_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFortyEightEP_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFortyEightEP_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFortyEightEP_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFortyEightEP_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFortyEightEP_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFortyEightEP_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFortyEightEP_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFortyEightEP_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFortyEightEP_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFortyEightEP_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFortyEightEP_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFortyEightEP_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFortyEightEP_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFortyEightEP_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFortyEightEP_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFortyEightEP_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFortyEightEP_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFortyEightEP_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFortyEightEP_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFortyEightEP_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFortyEightEP_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFortyEightEP_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFortyEightEP_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFortyEightEP_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFortyEightEP_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFortyEightEP_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFortyEightEP_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFortyEightEP_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFortyEightEP_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredFortyEightEP_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFortyEightEP_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFortyEightEP_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFortyEightEP_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFortyEightEP_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFortyEightEP_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFortyEightEP_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFortyEightEP_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredFortyEightEP_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFortyEightEP_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFortyEightEP_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFortyEightEP_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFortyEightEP_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFortyEightEP_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFortyEightEP_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFortyEightEP_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredFortyEightEP_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFortyEightEP_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFortyEightEP_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFortyEightEP_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredFortyEightEP_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredFortyEightEP_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFortyEightEP_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredFortyEightEP_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredFortyEightEP_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredFortyEightEP_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFortyEightEP_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredFortyEightEP_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredFortyEightEP_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFortyEightEP_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredFortyEightEP_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredFortyEightEP_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredFortyEightEP_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredFortyEightEP_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredFortyEightEP_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredFortyEightEP_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredFortyEightEP_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredFortyEightEP_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredFortyEightEP_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredFortyEightEP_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFortyEightEP_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredFortyEightEP_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredFortyEightEP_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredFortyEightEP_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredFortyEightEP_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredFortyEightEP_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredFortyEightEP_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredFortyEightEP_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredFortyEightEP_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredFortyEightEP_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredFortyEightEP_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredFortyEightEP_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredFortyEightEP_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredFortyEightEP_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredFortyEightEP_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredFortyEightEP_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredFortyEightEP_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredFortyEightEP_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredFortyEightEP_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredFortyEightEP_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredFortyEightEP_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredFortyEightEP_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredFortyEightEP_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredFortyEightEP_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredFortyEightEP_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredFortyEightEP_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredFortyEightEP_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredFortyEightEP_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredFortyEightEP_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredFortyEightEP_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredFortyEightEP_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredFortyEightEP_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredFortyEightEP_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredFortyEightEP_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredFortyEightEP_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredFortyEightEP_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredFortyEightEP_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredFortyEightEP_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredFortyEightEP_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredFortyEightEP_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredFortyEightEP_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_oneHundredFortyEightEP_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_oneHundredFortyEightEP_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredFortyEightEP_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_oneHundredFortyEightEP_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredFortyEightEP_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredFortyEightEP_1777 : Nat.Prime 1777 := by norm_num

private theorem prime_oneHundredFortyEightEP_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredFortyEightEP_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredFortyEightEP_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredFortyEightEP_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredFortyEightEP_2017 : Nat.Prime 2017 := by norm_num

private theorem prime_oneHundredFortyEightEP_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_oneHundredFortyEightEP_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_oneHundredFortyEightEP_2351 : Nat.Prime 2351 := by norm_num

private theorem prime_oneHundredFortyEightEP_2437 : Nat.Prime 2437 := by norm_num

private theorem prime_oneHundredFortyEightEP_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_oneHundredFortyEightEP_2659 : Nat.Prime 2659 := by norm_num

private theorem prime_oneHundredFortyEightEP_2663 : Nat.Prime 2663 := by norm_num

private theorem prime_oneHundredFortyEightEP_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_oneHundredFortyEightEP_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_oneHundredFortyEightEP_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_oneHundredFortyEightEP_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredFortyEightEP_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_oneHundredFortyEightEP_3137 : Nat.Prime 3137 := by norm_num

private theorem prime_oneHundredFortyEightEP_3163 : Nat.Prime 3163 := by norm_num

private theorem prime_oneHundredFortyEightEP_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_oneHundredFortyEightEP_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_oneHundredFortyEightEP_3469 : Nat.Prime 3469 := by norm_num

private theorem prime_oneHundredFortyEightEP_3511 : Nat.Prime 3511 := by norm_num

private theorem prime_oneHundredFortyEightEP_3559 : Nat.Prime 3559 := by norm_num

private theorem prime_oneHundredFortyEightEP_3571 : Nat.Prime 3571 := by norm_num

private theorem prime_oneHundredFortyEightEP_3613 : Nat.Prime 3613 := by norm_num

private theorem prime_oneHundredFortyEightEP_3637 : Nat.Prime 3637 := by norm_num

private theorem prime_oneHundredFortyEightEP_3643 : Nat.Prime 3643 := by norm_num

private theorem prime_oneHundredFortyEightEP_3697 : Nat.Prime 3697 := by norm_num

private theorem prime_oneHundredFortyEightEP_3701 : Nat.Prime 3701 := by norm_num

private theorem prime_oneHundredFortyEightEP_3833 : Nat.Prime 3833 := by norm_num

private theorem prime_oneHundredFortyEightEP_3989 : Nat.Prime 3989 := by norm_num

private theorem prime_oneHundredFortyEightEP_4049 : Nat.Prime 4049 := by norm_num

private theorem prime_oneHundredFortyEightEP_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_oneHundredFortyEightEP_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_oneHundredFortyEightEP_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_oneHundredFortyEightEP_4363 : Nat.Prime 4363 := by norm_num

private theorem prime_oneHundredFortyEightEP_4373 : Nat.Prime 4373 := by norm_num

private theorem prime_oneHundredFortyEightEP_4441 : Nat.Prime 4441 := by norm_num

private theorem prime_oneHundredFortyEightEP_4481 : Nat.Prime 4481 := by norm_num

private theorem prime_oneHundredFortyEightEP_4813 : Nat.Prime 4813 := by norm_num

private theorem prime_oneHundredFortyEightEP_4903 : Nat.Prime 4903 := by norm_num

private theorem prime_oneHundredFortyEightEP_4919 : Nat.Prime 4919 := by norm_num

private theorem prime_oneHundredFortyEightEP_4999 : Nat.Prime 4999 := by norm_num

private theorem prime_oneHundredFortyEightEP_5099 : Nat.Prime 5099 := by norm_num

private theorem prime_oneHundredFortyEightEP_5107 : Nat.Prime 5107 := by norm_num

private theorem prime_oneHundredFortyEightEP_5119 : Nat.Prime 5119 := by norm_num

private theorem prime_oneHundredFortyEightEP_5231 : Nat.Prime 5231 := by norm_num

private theorem prime_oneHundredFortyEightEP_5483 : Nat.Prime 5483 := by norm_num

private theorem prime_oneHundredFortyEightEP_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_oneHundredFortyEightEP_5869 : Nat.Prime 5869 := by norm_num

private theorem prime_oneHundredFortyEightEP_6197 : Nat.Prime 6197 := by norm_num

private theorem prime_oneHundredFortyEightEP_6299 : Nat.Prime 6299 := by norm_num

private theorem prime_oneHundredFortyEightEP_6451 : Nat.Prime 6451 := by norm_num

private theorem prime_oneHundredFortyEightEP_6473 : Nat.Prime 6473 := by norm_num

private theorem prime_oneHundredFortyEightEP_6791 : Nat.Prime 6791 := by norm_num

private theorem prime_oneHundredFortyEightEP_6841 : Nat.Prime 6841 := by norm_num

private theorem prime_oneHundredFortyEightEP_6907 : Nat.Prime 6907 := by norm_num

private theorem prime_oneHundredFortyEightEP_6917 : Nat.Prime 6917 := by norm_num

private theorem prime_oneHundredFortyEightEP_6961 : Nat.Prime 6961 := by norm_num

private theorem prime_oneHundredFortyEightEP_7193 : Nat.Prime 7193 := by norm_num

private theorem prime_oneHundredFortyEightEP_7351 : Nat.Prime 7351 := by norm_num

private theorem prime_oneHundredFortyEightEP_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredFortyEightEP_7993 : Nat.Prime 7993 := by norm_num

private theorem prime_oneHundredFortyEightEP_8111 : Nat.Prime 8111 := by norm_num

private theorem prime_oneHundredFortyEightEP_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredFortyEightEP_8461 : Nat.Prime 8461 := by norm_num

private theorem prime_oneHundredFortyEightEP_8537 : Nat.Prime 8537 := by norm_num

private theorem prime_oneHundredFortyEightEP_8741 : Nat.Prime 8741 := by norm_num

private theorem prime_oneHundredFortyEightEP_9041 : Nat.Prime 9041 := by norm_num

private theorem prime_oneHundredFortyEightEP_9133 : Nat.Prime 9133 := by norm_num

private theorem prime_oneHundredFortyEightEP_9199 : Nat.Prime 9199 := by norm_num

private theorem prime_oneHundredFortyEightEP_9257 : Nat.Prime 9257 := by norm_num

private theorem prime_oneHundredFortyEightEP_9461 : Nat.Prime 9461 := by norm_num

private theorem prime_oneHundredFortyEightEP_9623 : Nat.Prime 9623 := by norm_num

private theorem prime_oneHundredFortyEightEP_9767 : Nat.Prime 9767 := by norm_num

private theorem prime_oneHundredFortyEightEP_9901 : Nat.Prime 9901 := by norm_num

private theorem prime_oneHundredFortyEightEP_9941 : Nat.Prime 9941 := by norm_num

private theorem prime_oneHundredFortyEightEP_10487 : Nat.Prime 10487 := by norm_num

private theorem prime_oneHundredFortyEightEP_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredFortyEightEP_11399 : Nat.Prime 11399 := by norm_num

private theorem prime_oneHundredFortyEightEP_11411 : Nat.Prime 11411 := by norm_num

private theorem prime_oneHundredFortyEightEP_11909 : Nat.Prime 11909 := by norm_num

private theorem prime_oneHundredFortyEightEP_12277 : Nat.Prime 12277 := by norm_num

private theorem prime_oneHundredFortyEightEP_12437 : Nat.Prime 12437 := by norm_num

private theorem prime_oneHundredFortyEightEP_12823 : Nat.Prime 12823 := by norm_num

private theorem prime_oneHundredFortyEightEP_14401 : Nat.Prime 14401 := by norm_num

private theorem prime_oneHundredFortyEightEP_15733 : Nat.Prime 15733 := by norm_num

private theorem prime_oneHundredFortyEightEP_16127 : Nat.Prime 16127 := by norm_num

private theorem prime_oneHundredFortyEightEP_17053 : Nat.Prime 17053 := by norm_num

private theorem prime_oneHundredFortyEightEP_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFortyEightEP_17333 : Nat.Prime 17333 := by norm_num

private theorem prime_oneHundredFortyEightEP_18911 : Nat.Prime 18911 := by norm_num

private theorem prime_oneHundredFortyEightEP_19213 : Nat.Prime 19213 := by norm_num

private theorem prime_oneHundredFortyEightEP_19381 : Nat.Prime 19381 := by norm_num

private theorem prime_oneHundredFortyEightEP_20173 : Nat.Prime 20173 := by norm_num

private theorem prime_oneHundredFortyEightEP_20563 : Nat.Prime 20563 := by norm_num

private theorem prime_oneHundredFortyEightEP_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFortyEightEP_21149 : Nat.Prime 21149 := by norm_num

private theorem prime_oneHundredFortyEightEP_21491 : Nat.Prime 21491 := by norm_num

private theorem prime_oneHundredFortyEightEP_21773 : Nat.Prime 21773 := by norm_num

private theorem prime_oneHundredFortyEightEP_21839 : Nat.Prime 21839 := by norm_num

private theorem prime_oneHundredFortyEightEP_22109 : Nat.Prime 22109 := by norm_num

private theorem prime_oneHundredFortyEightEP_22277 : Nat.Prime 22277 := by norm_num

private theorem prime_oneHundredFortyEightEP_22741 : Nat.Prime 22741 := by norm_num

private theorem prime_oneHundredFortyEightEP_22769 : Nat.Prime 22769 := by norm_num

private theorem prime_oneHundredFortyEightEP_23087 : Nat.Prime 23087 := by norm_num

private theorem prime_oneHundredFortyEightEP_23629 : Nat.Prime 23629 := by norm_num

private theorem prime_oneHundredFortyEightEP_23747 : Nat.Prime 23747 := by norm_num

private theorem prime_oneHundredFortyEightEP_24419 : Nat.Prime 24419 := by norm_num

private theorem prime_oneHundredFortyEightEP_24917 : Nat.Prime 24917 := by norm_num

private theorem prime_oneHundredFortyEightEP_25793 : Nat.Prime 25793 := by norm_num

private theorem prime_oneHundredFortyEightEP_26641 : Nat.Prime 26641 := by norm_num

private theorem prime_oneHundredFortyEightEP_26647 : Nat.Prime 26647 := by norm_num

private theorem prime_oneHundredFortyEightEP_26717 : Nat.Prime 26717 := by norm_num

private theorem prime_oneHundredFortyEightEP_26893 : Nat.Prime 26893 := by norm_num

private theorem prime_oneHundredFortyEightEP_29611 : Nat.Prime 29611 := by norm_num

private theorem prime_oneHundredFortyEightEP_30181 : Nat.Prime 30181 := by norm_num

private theorem prime_oneHundredFortyEightEP_30223 : Nat.Prime 30223 := by norm_num

private theorem prime_oneHundredFortyEightEP_30269 : Nat.Prime 30269 := by norm_num

private theorem prime_oneHundredFortyEightEP_31771 : Nat.Prime 31771 := by norm_num

private theorem prime_oneHundredFortyEightEP_31883 : Nat.Prime 31883 := by norm_num

private theorem prime_oneHundredFortyEightEP_33013 : Nat.Prime 33013 := by norm_num

private theorem prime_oneHundredFortyEightEP_33073 : Nat.Prime 33073 := by norm_num

private theorem prime_oneHundredFortyEightEP_33757 : Nat.Prime 33757 := by norm_num

private theorem prime_oneHundredFortyEightEP_34687 : Nat.Prime 34687 := by norm_num

private theorem prime_oneHundredFortyEightEP_35051 : Nat.Prime 35051 := by norm_num

private theorem prime_oneHundredFortyEightEP_36017 : Nat.Prime 36017 := by norm_num

private theorem prime_oneHundredFortyEightEP_36529 : Nat.Prime 36529 := by norm_num

private theorem prime_oneHundredFortyEightEP_38447 : Nat.Prime 38447 := by norm_num

private theorem prime_oneHundredFortyEightEP_39163 : Nat.Prime 39163 := by norm_num

private theorem prime_oneHundredFortyEightEP_40241 : Nat.Prime 40241 := by norm_num

private theorem prime_oneHundredFortyEightEP_45181 : Nat.Prime 45181 := by norm_num

private theorem prime_oneHundredFortyEightEP_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredFortyEightEP_49477 : Nat.Prime 49477 := by norm_num

private theorem prime_oneHundredFortyEightEP_49939 : Nat.Prime 49939 := by norm_num

private theorem prime_oneHundredFortyEightEP_50329 : Nat.Prime 50329 := by norm_num

private theorem prime_oneHundredFortyEightEP_51929 : Nat.Prime 51929 := by norm_num

private theorem prime_oneHundredFortyEightEP_52639 : Nat.Prime 52639 := by norm_num

private theorem prime_oneHundredFortyEightEP_52919 : Nat.Prime 52919 := by norm_num

private theorem prime_oneHundredFortyEightEP_54647 : Nat.Prime 54647 := by norm_num

private theorem prime_oneHundredFortyEightEP_54941 : Nat.Prime 54941 := by norm_num

private theorem prime_oneHundredFortyEightEP_56597 : Nat.Prime 56597 := by norm_num

private theorem prime_oneHundredFortyEightEP_56909 : Nat.Prime 56909 := by norm_num

private theorem prime_oneHundredFortyEightEP_58997 : Nat.Prime 58997 := by norm_num

private theorem prime_oneHundredFortyEightEP_59887 : Nat.Prime 59887 := by norm_num

private theorem prime_oneHundredFortyEightEP_60589 : Nat.Prime 60589 := by norm_num

private theorem prime_oneHundredFortyEightEP_65551 : Nat.Prime 65551 := by norm_num

private theorem prime_oneHundredFortyEightEP_66791 : Nat.Prime 66791 := by norm_num

private theorem prime_oneHundredFortyEightEP_67217 : Nat.Prime 67217 := by norm_num

private theorem prime_oneHundredFortyEightEP_67339 : Nat.Prime 67339 := by norm_num

private theorem prime_oneHundredFortyEightEP_68213 : Nat.Prime 68213 := by norm_num

private theorem prime_oneHundredFortyEightEP_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredFortyEightEP_70439 : Nat.Prime 70439 := by norm_num

private theorem prime_oneHundredFortyEightEP_72923 : Nat.Prime 72923 := by norm_num

private theorem prime_oneHundredFortyEightEP_74731 : Nat.Prime 74731 := by norm_num

private theorem prime_oneHundredFortyEightEP_75367 : Nat.Prime 75367 := by norm_num

private theorem prime_oneHundredFortyEightEP_78853 : Nat.Prime 78853 := by norm_num

private theorem prime_oneHundredFortyEightEP_79549 : Nat.Prime 79549 := by norm_num

private theorem prime_oneHundredFortyEightEP_84913 : Nat.Prime 84913 := by norm_num

private theorem prime_oneHundredFortyEightEP_92507 : Nat.Prime 92507 := by norm_num

private theorem prime_oneHundredFortyEightEP_92593 : Nat.Prime 92593 := by norm_num

private theorem prime_oneHundredFortyEightEP_94999 : Nat.Prime 94999 := by norm_num

private theorem prime_oneHundredFortyEightEP_95603 : Nat.Prime 95603 := by norm_num

private theorem prime_oneHundredFortyEightEP_99559 : Nat.Prime 99559 := by norm_num

private theorem prime_oneHundredFortyEightEP_105529 : Nat.Prime 105529 := by norm_num

private theorem prime_oneHundredFortyEightEP_109253 : Nat.Prime 109253 := by norm_num

private theorem prime_oneHundredFortyEightEP_116189 : Nat.Prime 116189 := by norm_num

private theorem prime_oneHundredFortyEightEP_116279 : Nat.Prime 116279 := by norm_num

private theorem prime_oneHundredFortyEightEP_118621 : Nat.Prime 118621 := by norm_num

private theorem prime_oneHundredFortyEightEP_128983 : Nat.Prime 128983 := by norm_num

private theorem prime_oneHundredFortyEightEP_135929 : Nat.Prime 135929 := by norm_num

private theorem prime_oneHundredFortyEightEP_140339 : Nat.Prime 140339 := by norm_num

private theorem prime_oneHundredFortyEightEP_141233 : Nat.Prime 141233 := by norm_num

private theorem prime_oneHundredFortyEightEP_141539 : Nat.Prime 141539 := by norm_num

private theorem prime_oneHundredFortyEightEP_142897 : Nat.Prime 142897 := by norm_num

private theorem prime_oneHundredFortyEightEP_154667 : Nat.Prime 154667 := by norm_num

private theorem prime_oneHundredFortyEightEP_159937 : Nat.Prime 159937 := by norm_num

private theorem prime_oneHundredFortyEightEP_170099 : Nat.Prime 170099 := by norm_num

private theorem prime_oneHundredFortyEightEP_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFortyEightEP_171469 : Nat.Prime 171469 := by norm_num

private theorem prime_oneHundredFortyEightEP_172663 : Nat.Prime 172663 := by norm_num

private theorem prime_oneHundredFortyEightEP_174259 : Nat.Prime 174259 := by norm_num

private theorem prime_oneHundredFortyEightEP_175141 : Nat.Prime 175141 := by norm_num

private theorem prime_oneHundredFortyEightEP_178859 : Nat.Prime 178859 := by norm_num

private theorem prime_oneHundredFortyEightEP_203429 : Nat.Prime 203429 := by norm_num

private theorem prime_oneHundredFortyEightEP_203653 : Nat.Prime 203653 := by norm_num

private theorem prime_oneHundredFortyEightEP_231331 : Nat.Prime 231331 := by norm_num

private theorem prime_oneHundredFortyEightEP_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredFortyEightEP_247997 : Nat.Prime 247997 := by norm_num

private theorem prime_oneHundredFortyEightEP_255121 : Nat.Prime 255121 := by norm_num

private theorem prime_oneHundredFortyEightEP_263443 : Nat.Prime 263443 := by norm_num

private theorem prime_oneHundredFortyEightEP_267647 : Nat.Prime 267647 := by norm_num

private theorem prime_oneHundredFortyEightEP_268211 : Nat.Prime 268211 := by norm_num

private theorem prime_oneHundredFortyEightEP_273131 : Nat.Prime 273131 := by norm_num

private theorem prime_oneHundredFortyEightEP_273643 : Nat.Prime 273643 := by norm_num

private theorem prime_oneHundredFortyEightEP_292091 : Nat.Prime 292091 := by norm_num

private theorem prime_oneHundredFortyEightEP_299603 : Nat.Prime 299603 := by norm_num

private theorem prime_oneHundredFortyEightEP_309437 : Nat.Prime 309437 := by norm_num

private theorem prime_oneHundredFortyEightEP_316177 : Nat.Prime 316177 := by norm_num

private theorem prime_oneHundredFortyEightEP_317363 : Nat.Prime 317363 := by norm_num

private theorem prime_oneHundredFortyEightEP_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredFortyEightEP_406699 : Nat.Prime 406699 := by norm_num

private theorem prime_oneHundredFortyEightEP_434243 : Nat.Prime 434243 := by norm_num

private theorem prime_oneHundredFortyEightEP_512713 : Nat.Prime 512713 := by norm_num

private theorem prime_oneHundredFortyEightEP_539321 : Nat.Prime 539321 := by norm_num

private theorem prime_oneHundredFortyEightEP_546479 : Nat.Prime 546479 := by norm_num

private theorem prime_oneHundredFortyEightEP_560237 : Nat.Prime 560237 := by norm_num

private theorem prime_oneHundredFortyEightEP_570839 : Nat.Prime 570839 := by norm_num

private theorem prime_oneHundredFortyEightEP_640777 : Nat.Prime 640777 := by norm_num

private theorem prime_oneHundredFortyEightEP_645503 : Nat.Prime 645503 := by norm_num

private theorem prime_oneHundredFortyEightEP_647161 : Nat.Prime 647161 := by norm_num

private theorem prime_oneHundredFortyEightEP_649921 : Nat.Prime 649921 := by norm_num

private theorem prime_oneHundredFortyEightEP_652381 : Nat.Prime 652381 := by norm_num

private theorem prime_oneHundredFortyEightEP_695749 : Nat.Prime 695749 := by norm_num

private theorem prime_oneHundredFortyEightEP_729203 : Nat.Prime 729203 := by norm_num

private theorem prime_oneHundredFortyEightEP_868993 : Nat.Prime 868993 := by norm_num

private theorem prime_oneHundredFortyEightEP_897581 : Nat.Prime 897581 := by norm_num

private theorem prime_oneHundredFortyEightEP_946397 : Nat.Prime 946397 := by norm_num

private theorem prime_oneHundredFortyEightEP_952087 : Nat.Prime 952087 := by norm_num

private theorem prime_oneHundredFortyEightEP_955781 : Nat.Prime 955781 := by norm_num

private theorem prime_oneHundredFortyEightEP_956569 : Nat.Prime 956569 := by norm_num

private theorem prime_oneHundredFortyEightEP_976477 : Nat.Prime 976477 := by norm_num

private theorem prime_oneHundredFortyEightEP_1027853 : Nat.Prime 1027853 := by norm_num

private theorem prime_oneHundredFortyEightEP_1059343 : Nat.Prime 1059343 := by norm_num

private theorem prime_oneHundredFortyEightEP_1060529 : Nat.Prime 1060529 := by norm_num

private theorem prime_oneHundredFortyEightEP_1092851 : Nat.Prime 1092851 := by norm_num

private theorem prime_oneHundredFortyEightEP_1143749 : Nat.Prime 1143749 := by norm_num

private theorem prime_oneHundredFortyEightEP_1220507 : Nat.Prime 1220507 := by norm_num

private theorem prime_oneHundredFortyEightEP_1277803 : Nat.Prime 1277803 := by norm_num

private theorem prime_oneHundredFortyEightEP_1303859 : Nat.Prime 1303859 := by norm_num

private theorem prime_oneHundredFortyEightEP_1317571 : Nat.Prime 1317571 := by norm_num

private theorem prime_oneHundredFortyEightEP_1336619 : Nat.Prime 1336619 := by norm_num

private theorem prime_oneHundredFortyEightEP_1339411 : Nat.Prime 1339411 := by norm_num

private theorem prime_oneHundredFortyEightEP_1408417 : Nat.Prime 1408417 := by norm_num

private theorem prime_oneHundredFortyEightEP_1440913 : Nat.Prime 1440913 := by norm_num

private theorem prime_oneHundredFortyEightEP_1823051 : Nat.Prime 1823051 := by norm_num

private theorem prime_oneHundredFortyEightEP_1823911 : Nat.Prime 1823911 := by norm_num

private theorem prime_oneHundredFortyEightEP_1865119 : Nat.Prime 1865119 := by norm_num

private theorem prime_oneHundredFortyEightEP_1901191 : Nat.Prime 1901191 := by norm_num

private theorem prime_oneHundredFortyEightEP_1945301 : Nat.Prime 1945301 := by norm_num

private theorem prime_oneHundredFortyEightEP_1959583 : Nat.Prime 1959583 := by norm_num

private theorem prime_oneHundredFortyEightEP_2013911 : Nat.Prime 2013911 := by norm_num

private theorem prime_oneHundredFortyEightEP_2125933 : Nat.Prime 2125933 := by norm_num

private theorem prime_oneHundredFortyEightEP_2143331 : Nat.Prime 2143331 := by norm_num

private theorem prime_oneHundredFortyEightEP_2145641 : Nat.Prime 2145641 := by norm_num

private theorem prime_oneHundredFortyEightEP_2170039 : Nat.Prime 2170039 := by norm_num

private theorem prime_oneHundredFortyEightEP_2221861 : Nat.Prime 2221861 := by norm_num

private theorem prime_oneHundredFortyEightEP_2236261 : Nat.Prime 2236261 := by norm_num

private theorem prime_oneHundredFortyEightEP_2291717 : Nat.Prime 2291717 := by norm_num

private theorem prime_oneHundredFortyEightEP_2450837 : Nat.Prime 2450837 := by norm_num

private theorem prime_oneHundredFortyEightEP_2461309 : Nat.Prime 2461309 := by norm_num

private theorem prime_oneHundredFortyEightEP_2515757 : Nat.Prime 2515757 := by norm_num

private theorem prime_oneHundredFortyEightEP_2712713 : Nat.Prime 2712713 := by norm_num

private theorem prime_oneHundredFortyEightEP_2758541 : Nat.Prime 2758541 := by norm_num

private theorem prime_oneHundredFortyEightEP_3024493 : Nat.Prime 3024493 := by norm_num

private theorem prime_oneHundredFortyEightEP_3073757 : Nat.Prime 3073757 := by norm_num

private theorem prime_oneHundredFortyEightEP_3172423 : Nat.Prime 3172423 := by norm_num

private theorem prime_oneHundredFortyEightEP_3323561 : Nat.Prime 3323561 := by norm_num

private theorem prime_oneHundredFortyEightEP_3360299 : Nat.Prime 3360299 := by norm_num

private theorem prime_oneHundredFortyEightEP_3500593 : Nat.Prime 3500593 := by norm_num

private theorem prime_oneHundredFortyEightEP_3544217 : Nat.Prime 3544217 := by norm_num

private theorem prime_oneHundredFortyEightEP_3878209 : Nat.Prime 3878209 := by norm_num

private theorem prime_oneHundredFortyEightEP_4035481 : Nat.Prime 4035481 := by norm_num

private theorem prime_oneHundredFortyEightEP_4278881 : Nat.Prime 4278881 := by norm_num

private theorem prime_oneHundredFortyEightEP_4482227 : Nat.Prime 4482227 := by norm_num

private theorem prime_oneHundredFortyEightEP_4588121 : Nat.Prime 4588121 := by norm_num

private theorem prime_oneHundredFortyEightEP_4618993 : Nat.Prime 4618993 := by norm_num

private theorem prime_oneHundredFortyEightEP_4862353 : Nat.Prime 4862353 := by norm_num

private theorem prime_oneHundredFortyEightEP_4956509 : Nat.Prime 4956509 := by norm_num

private theorem prime_oneHundredFortyEightEP_5073559 : Nat.Prime 5073559 := by norm_num

private theorem prime_oneHundredFortyEightEP_5698093 : Nat.Prime 5698093 := by norm_num

private theorem prime_oneHundredFortyEightEP_5924987 : Nat.Prime 5924987 := by norm_num

private theorem prime_oneHundredFortyEightEP_6103847 : Nat.Prime 6103847 := by norm_num

private theorem prime_oneHundredFortyEightEP_6203251 : Nat.Prime 6203251 := by norm_num

private theorem prime_oneHundredFortyEightEP_6245311 : Nat.Prime 6245311 := by norm_num

private theorem prime_oneHundredFortyEightEP_6894161 : Nat.Prime 6894161 := by norm_num

private theorem prime_oneHundredFortyEightEP_7216241 : Nat.Prime 7216241 := by norm_num

private theorem prime_oneHundredFortyEightEP_8437493 : Nat.Prime 8437493 := by norm_num

private theorem prime_oneHundredFortyEightEP_8886391 : Nat.Prime 8886391 := by norm_num

private theorem prime_oneHundredFortyEightEP_9434767 : Nat.Prime 9434767 := by norm_num

private theorem prime_oneHundredFortyEightEP_10145657 : Nat.Prime 10145657 := by norm_num

private theorem prime_oneHundredFortyEightEP_10287787 : Nat.Prime 10287787 := by norm_num

private theorem prime_oneHundredFortyEightEP_10426733 : Nat.Prime 10426733 := by norm_num

private theorem prime_oneHundredFortyEightEP_10432259 : Nat.Prime 10432259 := by norm_num

private theorem prime_oneHundredFortyEightEP_10736413 : Nat.Prime 10736413 := by norm_num

private theorem prime_oneHundredFortyEightEP_10777141 : Nat.Prime 10777141 := by norm_num

private theorem prime_oneHundredFortyEightEP_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFortyEightEP_12209081 : Nat.Prime 12209081 := by norm_num

private theorem prime_oneHundredFortyEightEP_12263353 : Nat.Prime 12263353 := by norm_num

private theorem prime_oneHundredFortyEightEP_13000297 : Nat.Prime 13000297 := by norm_num

private theorem prime_oneHundredFortyEightEP_13432451 : Nat.Prime 13432451 := by norm_num

private theorem prime_oneHundredFortyEightEP_13802941 : Nat.Prime 13802941 := by norm_num

private theorem prime_oneHundredFortyEightEP_14097409 : Nat.Prime 14097409 := by norm_num

private theorem prime_oneHundredFortyEightEP_14988487 : Nat.Prime 14988487 := by norm_num

private theorem prime_oneHundredFortyEightEP_15677479 : Nat.Prime 15677479 := by norm_num

private theorem prime_oneHundredFortyEightEP_16462021 : Nat.Prime 16462021 := by norm_num

private theorem prime_oneHundredFortyEightEP_17808589 : Nat.Prime 17808589 := by norm_num

private theorem prime_oneHundredFortyEightEP_19780907 : Nat.Prime 19780907 := by norm_num

private theorem prime_oneHundredFortyEightEP_22933069 : Nat.Prime 22933069 := by norm_num

private theorem prime_oneHundredFortyEightEP_25261213 : Nat.Prime 25261213 := by norm_num

private theorem prime_oneHundredFortyEightEP_26356559 : Nat.Prime 26356559 := by norm_num

private theorem prime_oneHundredFortyEightEP_26732501 : Nat.Prime 26732501 := by norm_num

private theorem prime_oneHundredFortyEightEP_27973063 : Nat.Prime 27973063 := by norm_num

private theorem prime_oneHundredFortyEightEP_29413283 : Nat.Prime 29413283 := by norm_num

private theorem prime_oneHundredFortyEightEP_31278017 : Nat.Prime 31278017 := by
  apply lucas_primality 31278017 (3 : ZMod 31278017)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (11, 2), (577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (11, 2), (577, 1)] : List FactorBlock).map factorBlockValue).prod) = 31278017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31278017) ^ 15639008 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31278017) ^ 4468288 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31278017) ^ 2843456 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 31278017) ^ 54208 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_34648123 : Nat.Prime 34648123 := by
  apply lucas_primality 34648123 (2 : ZMod 34648123)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (137, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (137, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) = 34648123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_61
      · exact prime_oneHundredFortyEightEP_137
      · exact prime_oneHundredFortyEightEP_691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34648123) ^ 17324061 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34648123) ^ 11549374 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34648123) ^ 568002 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34648123) ^ 252906 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 34648123) ^ 50142 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_37965701 : Nat.Prime 37965701 := by
  apply lucas_primality 37965701 (2 : ZMod 37965701)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (37, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (37, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 37965701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_31
      · exact prime_oneHundredFortyEightEP_37
      · exact prime_oneHundredFortyEightEP_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37965701) ^ 18982850 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37965701) ^ 7593140 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37965701) ^ 1224700 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37965701) ^ 1026100 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37965701) ^ 114700 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_41111293 : Nat.Prime 41111293 := by
  apply lucas_primality 41111293 (2 : ZMod 41111293)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (92593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (92593, 1)] : List FactorBlock).map factorBlockValue).prod) = 41111293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_37
      · exact prime_oneHundredFortyEightEP_92593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41111293) ^ 20555646 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 41111293) ^ 13703764 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 41111293) ^ 1111116 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 41111293) ^ 444 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_46163069 : Nat.Prime 46163069 := by
  apply lucas_primality 46163069 (2 : ZMod 46163069)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (241, 1), (6841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (241, 1), (6841, 1)] : List FactorBlock).map factorBlockValue).prod) = 46163069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_241
      · exact prime_oneHundredFortyEightEP_6841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46163069) ^ 23081534 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46163069) ^ 6594724 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46163069) ^ 191548 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 46163069) ^ 6748 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_48180383 : Nat.Prime 48180383 := by
  apply lucas_primality 48180383 (5 : ZMod 48180383)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (560237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (560237, 1)] : List FactorBlock).map factorBlockValue).prod) = 48180383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_43
      · exact prime_oneHundredFortyEightEP_560237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 48180383) ^ 24090191 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 48180383) ^ 1120474 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 48180383) ^ 86 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_49183111 : Nat.Prime 49183111 := by
  apply lucas_primality 49183111 (3 : ZMod 49183111)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (546479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (546479, 1)] : List FactorBlock).map factorBlockValue).prod) = 49183111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_546479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 49183111) ^ 24591555 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 49183111) ^ 16394370 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 49183111) ^ 9836622 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 49183111) ^ 90 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_49737011 : Nat.Prime 49737011 := by
  apply lucas_primality 49737011 (2 : ZMod 49737011)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (127, 1), (39163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (127, 1), (39163, 1)] : List FactorBlock).map factorBlockValue).prod) = 49737011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_127
      · exact prime_oneHundredFortyEightEP_39163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49737011) ^ 24868505 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 49737011) ^ 9947402 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 49737011) ^ 391630 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 49737011) ^ 1270 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_50411887 : Nat.Prime 50411887 := by
  apply lucas_primality 50411887 (3 : ZMod 50411887)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (171469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (171469, 1)] : List FactorBlock).map factorBlockValue).prod) = 50411887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_171469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50411887) ^ 25205943 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 50411887) ^ 16803962 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 50411887) ^ 7201698 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 50411887) ^ 294 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_52713119 : Nat.Prime 52713119 := by
  apply lucas_primality 52713119 (7 : ZMod 52713119)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26356559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26356559, 1)] : List FactorBlock).map factorBlockValue).prod) = 52713119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_26356559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 52713119) ^ 26356559 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 52713119) ^ 2 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_1811
      · exact prime_oneHundredFortyEightEP_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_62666551 : Nat.Prime 62666551 := by
  apply lucas_primality 62666551 (3 : ZMod 62666551)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (157, 1), (887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (157, 1), (887, 1)] : List FactorBlock).map factorBlockValue).prod) = 62666551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_157
      · exact prime_oneHundredFortyEightEP_887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 62666551) ^ 31333275 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 62666551) ^ 20888850 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 62666551) ^ 12533310 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 62666551) ^ 399150 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 62666551) ^ 70650 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_63120899 : Nat.Prime 63120899 := by
  apply lucas_primality 63120899 (2 : ZMod 63120899)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (31, 1), (59887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (31, 1), (59887, 1)] : List FactorBlock).map factorBlockValue).prod) = 63120899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_31
      · exact prime_oneHundredFortyEightEP_59887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 63120899) ^ 31560449 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63120899) ^ 3712994 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63120899) ^ 2036158 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 63120899) ^ 1054 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_64171421 : Nat.Prime 64171421 := by
  apply lucas_primality 64171421 (2 : ZMod 64171421)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (167, 1), (19213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (167, 1), (19213, 1)] : List FactorBlock).map factorBlockValue).prod) = 64171421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_167
      · exact prime_oneHundredFortyEightEP_19213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 64171421) ^ 32085710 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 64171421) ^ 12834284 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 64171421) ^ 384260 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 64171421) ^ 3340 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_67473073 : Nat.Prime 67473073 := by
  apply lucas_primality 67473073 (5 : ZMod 67473073)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (233, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (233, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) = 67473073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_233
      · exact prime_oneHundredFortyEightEP_2011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 67473073) ^ 33736536 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 67473073) ^ 22491024 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 67473073) ^ 289584 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 67473073) ^ 33552 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_69159911 : Nat.Prime 69159911 := by
  apply lucas_primality 69159911 (7 : ZMod 69159911)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (43, 1), (9461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (43, 1), (9461, 1)] : List FactorBlock).map factorBlockValue).prod) = 69159911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_43
      · exact prime_oneHundredFortyEightEP_9461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 69159911) ^ 34579955 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 69159911) ^ 13831982 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 69159911) ^ 4068230 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 69159911) ^ 1608370 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 69159911) ^ 7310 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_69340759 : Nat.Prime 69340759 := by
  apply lucas_primality 69340759 (11 : ZMod 69340759)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (251, 1), (1123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (251, 1), (1123, 1)] : List FactorBlock).map factorBlockValue).prod) = 69340759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_41
      · exact prime_oneHundredFortyEightEP_251
      · exact prime_oneHundredFortyEightEP_1123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 69340759) ^ 34670379 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 69340759) ^ 23113586 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 69340759) ^ 1691238 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 69340759) ^ 276258 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 69340759) ^ 61746 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_77243077 : Nat.Prime 77243077 := by
  apply lucas_primality 77243077 (5 : ZMod 77243077)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2145641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2145641, 1)] : List FactorBlock).map factorBlockValue).prod) = 77243077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_2145641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 77243077) ^ 38621538 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 77243077) ^ 25747692 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 77243077) ^ 36 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_85577621 : Nat.Prime 85577621 := by
  apply lucas_primality 85577621 (3 : ZMod 85577621)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4278881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4278881, 1)] : List FactorBlock).map factorBlockValue).prod) = 85577621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_4278881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 85577621) ^ 42788810 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 85577621) ^ 17115524 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 85577621) ^ 20 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_96574273 : Nat.Prime 96574273 := by
  apply lucas_primality 96574273 (5 : ZMod 96574273)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (313, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (313, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) = 96574273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_313
      · exact prime_oneHundredFortyEightEP_1607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 96574273) ^ 48287136 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 96574273) ^ 32191424 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 96574273) ^ 308544 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 96574273) ^ 60096 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_97096339 : Nat.Prime 97096339 := by
  apply lucas_primality 97096339 (2 : ZMod 97096339)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (251, 1), (21491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (251, 1), (21491, 1)] : List FactorBlock).map factorBlockValue).prod) = 97096339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_251
      · exact prime_oneHundredFortyEightEP_21491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 97096339) ^ 48548169 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 97096339) ^ 32365446 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 97096339) ^ 386838 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 97096339) ^ 4518 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_115475119 : Nat.Prime 115475119 := by
  apply lucas_primality 115475119 (3 : ZMod 115475119)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (101, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (101, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod) = 115475119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_101
      · exact prime_oneHundredFortyEightEP_1019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 115475119) ^ 57737559 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 115475119) ^ 38491706 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 115475119) ^ 10497738 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 115475119) ^ 6792654 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 115475119) ^ 1143318 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 115475119) ^ 113322 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_118163399 : Nat.Prime 118163399 := by
  apply lucas_primality 118163399 (7 : ZMod 118163399)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (1129, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (1129, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) = 118163399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_43
      · exact prime_oneHundredFortyEightEP_1129
      · exact prime_oneHundredFortyEightEP_1217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 118163399) ^ 59081699 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 118163399) ^ 2747986 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 118163399) ^ 104662 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 118163399) ^ 97094 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_120905251 : Nat.Prime 120905251 := by
  apply lucas_primality 120905251 (2 : ZMod 120905251)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (23, 1), (43, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (23, 1), (43, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) = 120905251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_43
      · exact prime_oneHundredFortyEightEP_163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 120905251) ^ 60452625 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 120905251) ^ 40301750 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 120905251) ^ 24181050 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 120905251) ^ 5256750 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 120905251) ^ 2811750 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 120905251) ^ 741750 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_125176811 : Nat.Prime 125176811 := by
  apply lucas_primality 125176811 (11 : ZMod 125176811)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (23, 1), (49477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (23, 1), (49477, 1)] : List FactorBlock).map factorBlockValue).prod) = 125176811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_49477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 125176811) ^ 62588405 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 125176811) ^ 25035362 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 125176811) ^ 11379710 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 125176811) ^ 5442470 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 125176811) ^ 2530 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_146401991 : Nat.Prime 146401991 := by
  apply lucas_primality 146401991 (7 : ZMod 146401991)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (229, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (229, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) = 146401991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_229
      · exact prime_oneHundredFortyEightEP_9133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 146401991) ^ 73200995 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 146401991) ^ 29280398 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 146401991) ^ 20914570 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 146401991) ^ 639310 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 146401991) ^ 16030 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_161419241 : Nat.Prime 161419241 := by
  apply lucas_primality 161419241 (3 : ZMod 161419241)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (4035481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (4035481, 1)] : List FactorBlock).map factorBlockValue).prod) = 161419241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_4035481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 161419241) ^ 80709620 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 161419241) ^ 32283848 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 161419241) ^ 40 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_163199293 : Nat.Prime 163199293 := by
  apply lucas_primality 163199293 (2 : ZMod 163199293)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2663, 1), (5107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2663, 1), (5107, 1)] : List FactorBlock).map factorBlockValue).prod) = 163199293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_2663
      · exact prime_oneHundredFortyEightEP_5107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 163199293) ^ 81599646 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 163199293) ^ 54399764 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 163199293) ^ 61284 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 163199293) ^ 31956 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_167287453 : Nat.Prime 167287453 := by
  apply lucas_primality 167287453 (2 : ZMod 167287453)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3637, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3637, 1), (3833, 1)] : List FactorBlock).map factorBlockValue).prod) = 167287453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_3637
      · exact prime_oneHundredFortyEightEP_3833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 167287453) ^ 83643726 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 167287453) ^ 55762484 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 167287453) ^ 45996 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 167287453) ^ 43644 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_175825693 : Nat.Prime 175825693 := by
  apply lucas_primality 175825693 (5 : ZMod 175825693)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (97, 1), (7193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (97, 1), (7193, 1)] : List FactorBlock).map factorBlockValue).prod) = 175825693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_97
      · exact prime_oneHundredFortyEightEP_7193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 175825693) ^ 87912846 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 175825693) ^ 58608564 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 175825693) ^ 25117956 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 175825693) ^ 1812636 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 175825693) ^ 24444 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_188624041 : Nat.Prime 188624041 := by
  apply lucas_primality 188624041 (26 : ZMod 188624041)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (142897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (142897, 1)] : List FactorBlock).map factorBlockValue).prod) = 188624041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_142897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 188624041) ^ 94312020 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (26 : ZMod 188624041) ^ 62874680 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (26 : ZMod 188624041) ^ 37724808 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (26 : ZMod 188624041) ^ 17147640 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (26 : ZMod 188624041) ^ 1320 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_230559941 : Nat.Prime 230559941 := by
  apply lucas_primality 230559941 (2 : ZMod 230559941)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 2), (68213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 2), (68213, 1)] : List FactorBlock).map factorBlockValue).prod) = 230559941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_68213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 230559941) ^ 115279970 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 230559941) ^ 46111988 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 230559941) ^ 17735380 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 230559941) ^ 3380 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_249425623 : Nat.Prime 249425623 := by
  apply lucas_primality 249425623 (3 : ZMod 249425623)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (4618993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (4618993, 1)] : List FactorBlock).map factorBlockValue).prod) = 249425623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_4618993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 249425623) ^ 124712811 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 249425623) ^ 83141874 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 249425623) ^ 54 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_249569597 : Nat.Prime 249569597 := by
  apply lucas_primality 249569597 (2 : ZMod 249569597)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (2712713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (2712713, 1)] : List FactorBlock).map factorBlockValue).prod) = 249569597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_2712713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 249569597) ^ 124784798 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 249569597) ^ 10850852 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 249569597) ^ 92 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_263066689 : Nat.Prime 263066689 := by
  apply lucas_primality 263066689 (11 : ZMod 263066689)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (157, 1), (2909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (157, 1), (2909, 1)] : List FactorBlock).map factorBlockValue).prod) = 263066689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_157
      · exact prime_oneHundredFortyEightEP_2909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 263066689) ^ 131533344 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 263066689) ^ 87688896 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 263066689) ^ 1675584 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 263066689) ^ 90432 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_277287511 : Nat.Prime 277287511 := by
  apply lucas_primality 277287511 (6 : ZMod 277287511)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (41, 1), (89, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (41, 1), (89, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) = 277287511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_41
      · exact prime_oneHundredFortyEightEP_89
      · exact prime_oneHundredFortyEightEP_149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 277287511) ^ 138643755 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 92429170 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 55457502 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 16311030 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 6763110 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 3115590 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 277287511) ^ 1860990 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_308010277 : Nat.Prime 308010277 := by
  apply lucas_primality 308010277 (2 : ZMod 308010277)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (7, 2), (29, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (7, 2), (29, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 308010277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_29
      · exact prime_oneHundredFortyEightEP_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 308010277) ^ 154005138 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 308010277) ^ 102670092 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 308010277) ^ 44001468 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 308010277) ^ 10621044 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 308010277) ^ 1381212 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_312967771 : Nat.Prime 312967771 := by
  apply lucas_primality 312967771 (2 : ZMod 312967771)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (10432259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (10432259, 1)] : List FactorBlock).map factorBlockValue).prod) = 312967771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_10432259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 312967771) ^ 156483885 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 312967771) ^ 104322590 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 312967771) ^ 62593554 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 312967771) ^ 30 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_337245151 : Nat.Prime 337245151 := by
  apply lucas_primality 337245151 (3 : ZMod 337245151)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 2), (17, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 2), (17, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) = 337245151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 337245151) ^ 168622575 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 337245151) ^ 112415050 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 337245151) ^ 67449030 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 337245151) ^ 30658650 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 337245151) ^ 19837950 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 337245151) ^ 308550 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_340689277 : Nat.Prime 340689277 := by
  apply lucas_primality 340689277 (2 : ZMod 340689277)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (47, 1), (271, 1), (743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (47, 1), (271, 1), (743, 1)] : List FactorBlock).map factorBlockValue).prod) = 340689277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_47
      · exact prime_oneHundredFortyEightEP_271
      · exact prime_oneHundredFortyEightEP_743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 340689277) ^ 170344638 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 340689277) ^ 113563092 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 340689277) ^ 7248708 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 340689277) ^ 1257156 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 340689277) ^ 458532 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_358474211 : Nat.Prime 358474211 := by
  apply lucas_primality 358474211 (2 : ZMod 358474211)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1777, 1), (20173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1777, 1), (20173, 1)] : List FactorBlock).map factorBlockValue).prod) = 358474211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_1777
      · exact prime_oneHundredFortyEightEP_20173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 358474211) ^ 179237105 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 358474211) ^ 71694842 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 358474211) ^ 201730 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 358474211) ^ 17770 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_377155549 : Nat.Prime 377155549 := by
  apply lucas_primality 377155549 (2 : ZMod 377155549)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 2), (11, 2), (19, 1), (31, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 2), (11, 2), (19, 1), (31, 1)] : List FactorBlock).map factorBlockValue).prod) = 377155549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_31
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 377155549) ^ 188577774 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 377155549) ^ 125718516 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 377155549) ^ 53879364 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 377155549) ^ 34286868 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 377155549) ^ 19850292 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 377155549) ^ 12166308 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_393024829 : Nat.Prime 393024829 := by
  apply lucas_primality 393024829 (2 : ZMod 393024829)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (23, 1), (203429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (23, 1), (203429, 1)] : List FactorBlock).map factorBlockValue).prod) = 393024829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_203429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 393024829) ^ 196512414 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 393024829) ^ 131008276 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 393024829) ^ 56146404 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 393024829) ^ 17088036 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 393024829) ^ 1932 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_399233077 : Nat.Prime 399233077 := by
  apply lucas_primality 399233077 (5 : ZMod 399233077)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (3024493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (3024493, 1)] : List FactorBlock).map factorBlockValue).prod) = 399233077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_3024493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 399233077) ^ 199616538 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 399233077) ^ 133077692 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 399233077) ^ 36293916 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 399233077) ^ 132 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_462203219 : Nat.Prime 462203219 := by
  apply lucas_primality 462203219 (2 : ZMod 462203219)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (997, 1), (7993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (997, 1), (7993, 1)] : List FactorBlock).map factorBlockValue).prod) = 462203219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_29
      · exact prime_oneHundredFortyEightEP_997
      · exact prime_oneHundredFortyEightEP_7993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 462203219) ^ 231101609 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 462203219) ^ 15938042 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 462203219) ^ 463594 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 462203219) ^ 57826 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_507282851 : Nat.Prime 507282851 := by
  apply lucas_primality 507282851 (2 : ZMod 507282851)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (10145657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (10145657, 1)] : List FactorBlock).map factorBlockValue).prod) = 507282851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_10145657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 507282851) ^ 253641425 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 507282851) ^ 101456570 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 507282851) ^ 50 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_518727653 : Nat.Prime 518727653 := by
  apply lucas_primality 518727653 (2 : ZMod 518727653)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (2125933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (2125933, 1)] : List FactorBlock).map factorBlockValue).prod) = 518727653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_61
      · exact prime_oneHundredFortyEightEP_2125933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 518727653) ^ 259363826 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 518727653) ^ 8503732 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 518727653) ^ 244 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_546800473 : Nat.Prime 546800473 := by
  apply lucas_primality 546800473 (13 : ZMod 546800473)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1091, 1), (6961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1091, 1), (6961, 1)] : List FactorBlock).map factorBlockValue).prod) = 546800473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_1091
      · exact prime_oneHundredFortyEightEP_6961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 546800473) ^ 273400236 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 546800473) ^ 182266824 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 546800473) ^ 501192 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 546800473) ^ 78552 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_627247001 : Nat.Prime 627247001 := by
  apply lucas_primality 627247001 (3 : ZMod 627247001)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (19, 1), (33013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (19, 1), (33013, 1)] : List FactorBlock).map factorBlockValue).prod) = 627247001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_33013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 627247001) ^ 313623500 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 627247001) ^ 125449400 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 627247001) ^ 33013000 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 627247001) ^ 19000 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_632350777 : Nat.Prime 632350777 := by
  apply lucas_primality 632350777 (5 : ZMod 632350777)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (43, 1), (26641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (43, 1), (26641, 1)] : List FactorBlock).map factorBlockValue).prod) = 632350777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_43
      · exact prime_oneHundredFortyEightEP_26641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 632350777) ^ 316175388 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 632350777) ^ 210783592 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 632350777) ^ 27493512 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 632350777) ^ 14705832 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 632350777) ^ 23736 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_641450713 : Nat.Prime 641450713 := by
  apply lucas_primality 641450713 (5 : ZMod 641450713)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (307, 1), (12437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (307, 1), (12437, 1)] : List FactorBlock).map factorBlockValue).prod) = 641450713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_307
      · exact prime_oneHundredFortyEightEP_12437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 641450713) ^ 320725356 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 641450713) ^ 213816904 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 641450713) ^ 91635816 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 641450713) ^ 2089416 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 641450713) ^ 51576 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_697713433 : Nat.Prime 697713433 := by
  apply lucas_primality 697713433 (5 : ZMod 697713433)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (2236261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (2236261, 1)] : List FactorBlock).map factorBlockValue).prod) = 697713433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_2236261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 697713433) ^ 348856716 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 697713433) ^ 232571144 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 697713433) ^ 53670264 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 697713433) ^ 312 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_17203
      · exact prime_oneHundredFortyEightEP_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_716948423 : Nat.Prime 716948423 := by
  apply lucas_primality 716948423 (5 : ZMod 716948423)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (358474211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (358474211, 1)] : List FactorBlock).map factorBlockValue).prod) = 716948423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_358474211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 716948423) ^ 358474211 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 716948423) ^ 2 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_719730169 : Nat.Prime 719730169 := by
  apply lucas_primality 719730169 (39 : ZMod 719730169)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (1303859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (1303859, 1)] : List FactorBlock).map factorBlockValue).prod) = 719730169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_1303859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (39 : ZMod 719730169) ^ 359865084 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (39 : ZMod 719730169) ^ 239910056 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (39 : ZMod 719730169) ^ 31292616 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (39 : ZMod 719730169) ^ 552 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_751674467 : Nat.Prime 751674467 := by
  apply lucas_primality 751674467 (2 : ZMod 751674467)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (19780907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (19780907, 1)] : List FactorBlock).map factorBlockValue).prod) = 751674467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_19780907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 751674467) ^ 375837233 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 751674467) ^ 39561814 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 751674467) ^ 38 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_770057053 : Nat.Prime 770057053 := by
  apply lucas_primality 770057053 (2 : ZMod 770057053)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (64171421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (64171421, 1)] : List FactorBlock).map factorBlockValue).prod) = 770057053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_64171421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 770057053) ^ 385028526 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 770057053) ^ 256685684 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 770057053) ^ 12 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_788993147 : Nat.Prime 788993147 := by
  apply lucas_primality 788993147 (2 : ZMod 788993147)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5869, 1), (67217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5869, 1), (67217, 1)] : List FactorBlock).map factorBlockValue).prod) = 788993147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5869
      · exact prime_oneHundredFortyEightEP_67217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 788993147) ^ 394496573 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 788993147) ^ 134434 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 788993147) ^ 11738 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_908057209 : Nat.Prime 908057209 := by
  apply lucas_primality 908057209 (13 : ZMod 908057209)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (1220507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (1220507, 1)] : List FactorBlock).map factorBlockValue).prod) = 908057209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_31
      · exact prime_oneHundredFortyEightEP_1220507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 908057209) ^ 454028604 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 908057209) ^ 302685736 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 908057209) ^ 29292168 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 908057209) ^ 744 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_930426883 : Nat.Prime 930426883 := by
  apply lucas_primality 930426883 (2 : ZMod 930426883)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (2013911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (2013911, 1)] : List FactorBlock).map factorBlockValue).prod) = 930426883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_2013911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 930426883) ^ 465213441 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 930426883) ^ 310142294 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 930426883) ^ 132918126 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 930426883) ^ 84584262 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 930426883) ^ 462 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1201054009 : Nat.Prime 1201054009 := by
  apply lucas_primality 1201054009 (17 : ZMod 1201054009)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (649921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (649921, 1)] : List FactorBlock).map factorBlockValue).prod) = 1201054009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_649921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1201054009) ^ 600527004 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (17 : ZMod 1201054009) ^ 400351336 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (17 : ZMod 1201054009) ^ 171579144 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (17 : ZMod 1201054009) ^ 109186728 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (17 : ZMod 1201054009) ^ 1848 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1296816439 : Nat.Prime 1296816439 := by
  apply lucas_primality 1296816439 (3 : ZMod 1296816439)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2741, 1), (78853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2741, 1), (78853, 1)] : List FactorBlock).map factorBlockValue).prod) = 1296816439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_2741
      · exact prime_oneHundredFortyEightEP_78853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1296816439) ^ 648408219 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1296816439) ^ 432272146 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1296816439) ^ 473118 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1296816439) ^ 16446 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1402219501 : Nat.Prime 1402219501 := by
  apply lucas_primality 1402219501 (6 : ZMod 1402219501)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (11, 1), (17, 1), (4999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (11, 1), (17, 1), (4999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1402219501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_4999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1402219501) ^ 701109750 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1402219501) ^ 467406500 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1402219501) ^ 280443900 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1402219501) ^ 127474500 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1402219501) ^ 82483500 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 1402219501) ^ 280500 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1631992931 : Nat.Prime 1631992931 := by
  apply lucas_primality 1631992931 (2 : ZMod 1631992931)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (163199293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (163199293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1631992931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_163199293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1631992931) ^ 815996465 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1631992931) ^ 326398586 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1631992931) ^ 10 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1654287587 : Nat.Prime 1654287587 := by
  apply lucas_primality 1654287587 (2 : ZMod 1654287587)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (118163399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (118163399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1654287587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_118163399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1654287587) ^ 827143793 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1654287587) ^ 236326798 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1654287587) ^ 14 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1677540173 : Nat.Prime 1677540173 := by
  apply lucas_primality 1677540173 (2 : ZMod 1677540173)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (19, 1), (173, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (19, 1), (173, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) = 1677540173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_173
      · exact prime_oneHundredFortyEightEP_1657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1677540173) ^ 838770086 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1677540173) ^ 239648596 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1677540173) ^ 152503652 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1677540173) ^ 88291588 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1677540173) ^ 9696764 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1677540173) ^ 1012396 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1740490439 : Nat.Prime 1740490439 := by
  apply lucas_primality 1740490439 (7 : ZMod 1740490439)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8741, 1), (99559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8741, 1), (99559, 1)] : List FactorBlock).map factorBlockValue).prod) = 1740490439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_8741
      · exact prime_oneHundredFortyEightEP_99559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1740490439) ^ 870245219 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1740490439) ^ 199118 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1740490439) ^ 17482 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1765947563 : Nat.Prime 1765947563 := by
  apply lucas_primality 1765947563 (2 : ZMod 1765947563)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3461, 1), (255121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3461, 1), (255121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1765947563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3461
      · exact prime_oneHundredFortyEightEP_255121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1765947563) ^ 882973781 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1765947563) ^ 510242 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1765947563) ^ 6922 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1787220067 : Nat.Prime 1787220067 := by
  apply lucas_primality 1787220067 (2 : ZMod 1787220067)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (277, 1), (56597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (277, 1), (56597, 1)] : List FactorBlock).map factorBlockValue).prod) = 1787220067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_277
      · exact prime_oneHundredFortyEightEP_56597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1787220067) ^ 893610033 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1787220067) ^ 595740022 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1787220067) ^ 94064214 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1787220067) ^ 6452058 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1787220067) ^ 31578 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1853679307 : Nat.Prime 1853679307 := by
  apply lucas_primality 1853679307 (2 : ZMod 1853679307)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2659, 1), (116189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2659, 1), (116189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1853679307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_2659
      · exact prime_oneHundredFortyEightEP_116189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1853679307) ^ 926839653 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1853679307) ^ 617893102 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1853679307) ^ 697134 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1853679307) ^ 15954 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2195951413 : Nat.Prime 2195951413 := by
  apply lucas_primality 2195951413 (5 : ZMod 2195951413)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (127, 1), (1440913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (127, 1), (1440913, 1)] : List FactorBlock).map factorBlockValue).prod) = 2195951413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_127
      · exact prime_oneHundredFortyEightEP_1440913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2195951413) ^ 1097975706 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2195951413) ^ 731983804 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2195951413) ^ 17290956 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2195951413) ^ 1524 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2376938591 : Nat.Prime 2376938591 := by
  apply lucas_primality 2376938591 (11 : ZMod 2376938591)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (827, 1), (22109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (827, 1), (22109, 1)] : List FactorBlock).map factorBlockValue).prod) = 2376938591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_827
      · exact prime_oneHundredFortyEightEP_22109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2376938591) ^ 1188469295 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2376938591) ^ 475387718 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2376938591) ^ 182841430 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2376938591) ^ 2874170 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 2376938591) ^ 107510 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_47
      · exact prime_oneHundredFortyEightEP_71
      · exact prime_oneHundredFortyEightEP_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2658674663 : Nat.Prime 2658674663 := by
  apply lucas_primality 2658674663 (5 : ZMod 2658674663)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (71, 1), (56909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (71, 1), (56909, 1)] : List FactorBlock).map factorBlockValue).prod) = 2658674663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_47
      · exact prime_oneHundredFortyEightEP_71
      · exact prime_oneHundredFortyEightEP_56909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2658674663) ^ 1329337331 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2658674663) ^ 379810666 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2658674663) ^ 56567546 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2658674663) ^ 37446122 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2658674663) ^ 46718 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2769784141 : Nat.Prime 2769784141 := by
  apply lucas_primality 2769784141 (2 : ZMod 2769784141)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (46163069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (46163069, 1)] : List FactorBlock).map factorBlockValue).prod) = 2769784141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_46163069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2769784141) ^ 1384892070 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2769784141) ^ 923261380 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2769784141) ^ 553956828 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2769784141) ^ 60 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_3421583713 : Nat.Prime 3421583713 := by
  apply lucas_primality 3421583713 (10 : ZMod 3421583713)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (199, 1), (227, 1), (263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (199, 1), (227, 1), (263, 1)] : List FactorBlock).map factorBlockValue).prod) = 3421583713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_199
      · exact prime_oneHundredFortyEightEP_227
      · exact prime_oneHundredFortyEightEP_263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3421583713) ^ 1710791856 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3421583713) ^ 1140527904 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3421583713) ^ 17193888 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3421583713) ^ 15073056 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (10 : ZMod 3421583713) ^ 13009824 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_4358816123 : Nat.Prime 4358816123 := by
  apply lucas_primality 4358816123 (2 : ZMod 4358816123)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (113, 1), (316177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (113, 1), (316177, 1)] : List FactorBlock).map factorBlockValue).prod) = 4358816123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_61
      · exact prime_oneHundredFortyEightEP_113
      · exact prime_oneHundredFortyEightEP_316177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4358816123) ^ 2179408061 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4358816123) ^ 71456002 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4358816123) ^ 38573594 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4358816123) ^ 13786 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_4630863227 : Nat.Prime 4630863227 := by
  apply lucas_primality 4630863227 (2 : ZMod 4630863227)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (97, 1), (2170039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (97, 1), (2170039, 1)] : List FactorBlock).map factorBlockValue).prod) = 4630863227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_97
      · exact prime_oneHundredFortyEightEP_2170039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4630863227) ^ 2315431613 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4630863227) ^ 420987566 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4630863227) ^ 47740858 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4630863227) ^ 2134 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_4692029851 : Nat.Prime 4692029851 := by
  apply lucas_primality 4692029851 (2 : ZMod 4692029851)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (10426733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (10426733, 1)] : List FactorBlock).map factorBlockValue).prod) = 4692029851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_10426733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4692029851) ^ 2346014925 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4692029851) ^ 1564009950 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4692029851) ^ 938405970 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4692029851) ^ 450 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_5210386787 : Nat.Prime 5210386787 := by
  apply lucas_primality 5210386787 (2 : ZMod 5210386787)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3613, 1), (65551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3613, 1), (65551, 1)] : List FactorBlock).map factorBlockValue).prod) = 5210386787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_3613
      · exact prime_oneHundredFortyEightEP_65551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5210386787) ^ 2605193393 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5210386787) ^ 473671526 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5210386787) ^ 1442122 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5210386787) ^ 79486 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_5469296603 : Nat.Prime 5469296603 := by
  apply lucas_primality 5469296603 (5 : ZMod 5469296603)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (5073559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (5073559, 1)] : List FactorBlock).map factorBlockValue).prod) = 5469296603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_5073559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5469296603) ^ 2734648301 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5469296603) ^ 781328086 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5469296603) ^ 497208782 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 5469296603) ^ 1078 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_31
      · exact prime_oneHundredFortyEightEP_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_6197071987 : Nat.Prime 6197071987 := by
  apply lucas_primality 6197071987 (2 : ZMod 6197071987)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (49183111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (49183111, 1)] : List FactorBlock).map factorBlockValue).prod) = 6197071987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_49183111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6197071987) ^ 3098535993 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6197071987) ^ 2065690662 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6197071987) ^ 885295998 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6197071987) ^ 126 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_6293333183 : Nat.Prime 6293333183 := by
  apply lucas_primality 6293333183 (5 : ZMod 6293333183)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (47, 1), (67, 1), (113, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (47, 1), (67, 1), (113, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 6293333183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_37
      · exact prime_oneHundredFortyEightEP_47
      · exact prime_oneHundredFortyEightEP_67
      · exact prime_oneHundredFortyEightEP_113
      · exact prime_oneHundredFortyEightEP_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6293333183) ^ 3146666591 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 6293333183) ^ 170090086 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 6293333183) ^ 133900706 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 6293333183) ^ 93930346 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 6293333183) ^ 55693214 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 6293333183) ^ 26331938 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_6410691113 : Nat.Prime 6410691113 := by
  apply lucas_primality 6410691113 (3 : ZMod 6410691113)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (673, 1), (170099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (673, 1), (170099, 1)] : List FactorBlock).map factorBlockValue).prod) = 6410691113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_673
      · exact prime_oneHundredFortyEightEP_170099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6410691113) ^ 3205345556 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6410691113) ^ 915813016 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6410691113) ^ 9525544 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 6410691113) ^ 37688 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_7757252843 : Nat.Prime 7757252843 := by
  apply lucas_primality 7757252843 (2 : ZMod 7757252843)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (281, 1), (13802941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (281, 1), (13802941, 1)] : List FactorBlock).map factorBlockValue).prod) = 7757252843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_281
      · exact prime_oneHundredFortyEightEP_13802941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7757252843) ^ 3878626421 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7757252843) ^ 27605882 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7757252843) ^ 562 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_8043681439 : Nat.Prime 8043681439 := by
  apply lucas_primality 8043681439 (6 : ZMod 8043681439)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (683, 1), (50329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (683, 1), (50329, 1)] : List FactorBlock).map factorBlockValue).prod) = 8043681439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_683
      · exact prime_oneHundredFortyEightEP_50329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8043681439) ^ 4021840719 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 8043681439) ^ 2681227146 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 8043681439) ^ 618744726 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 8043681439) ^ 11776986 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 8043681439) ^ 159822 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_9176125001 : Nat.Prime 9176125001 := by
  apply lucas_primality 9176125001 (3 : ZMod 9176125001)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 6), (7, 1), (10487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 6), (7, 1), (10487, 1)] : List FactorBlock).map factorBlockValue).prod) = 9176125001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_10487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9176125001) ^ 4588062500 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9176125001) ^ 1835225000 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9176125001) ^ 1310875000 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9176125001) ^ 875000 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_9662531407 : Nat.Prime 9662531407 := by
  apply lucas_primality 9662531407 (5 : ZMod 9662531407)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (146401991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (146401991, 1)] : List FactorBlock).map factorBlockValue).prod) = 9662531407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_146401991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9662531407) ^ 4831265703 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 9662531407) ^ 3220843802 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 9662531407) ^ 878411946 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 9662531407) ^ 66 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_10037277923 : Nat.Prime 10037277923 := by
  apply lucas_primality 10037277923 (2 : ZMod 10037277923)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (716948423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (716948423, 1)] : List FactorBlock).map factorBlockValue).prod) = 10037277923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_716948423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10037277923) ^ 5018638961 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10037277923) ^ 1433896846 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10037277923) ^ 14 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_10250375021 : Nat.Prime 10250375021 := by
  apply lucas_primality 10250375021 (2 : ZMod 10250375021)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (571, 1), (897581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (571, 1), (897581, 1)] : List FactorBlock).map factorBlockValue).prod) = 10250375021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_571
      · exact prime_oneHundredFortyEightEP_897581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10250375021) ^ 5125187510 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10250375021) ^ 2050075004 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10250375021) ^ 17951620 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10250375021) ^ 11420 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_11088369973 : Nat.Prime 11088369973 := by
  apply lucas_primality 11088369973 (2 : ZMod 11088369973)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (308010277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (308010277, 1)] : List FactorBlock).map factorBlockValue).prod) = 11088369973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_308010277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11088369973) ^ 5544184986 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11088369973) ^ 3696123324 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11088369973) ^ 36 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_11331744007 : Nat.Prime 11331744007 := by
  apply lucas_primality 11331744007 (6 : ZMod 11331744007)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (23, 1), (2017, 1), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (23, 1), (2017, 1), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) = 11331744007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_2017
      · exact prime_oneHundredFortyEightEP_3701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11331744007) ^ 5665872003 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 11331744007) ^ 3777248002 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 11331744007) ^ 1030158546 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 11331744007) ^ 492684522 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 11331744007) ^ 5618118 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 11331744007) ^ 3061806 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_12112361333 : Nat.Prime 12112361333 := by
  apply lucas_primality 12112361333 (2 : ZMod 12112361333)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (22277, 1), (135929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (22277, 1), (135929, 1)] : List FactorBlock).map factorBlockValue).prod) = 12112361333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_22277
      · exact prime_oneHundredFortyEightEP_135929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12112361333) ^ 6056180666 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12112361333) ^ 543716 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12112361333) ^ 89108 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_15514505687 : Nat.Prime 15514505687 := by
  apply lucas_primality 15514505687 (5 : ZMod 15514505687)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7757252843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7757252843, 1)] : List FactorBlock).map factorBlockValue).prod) = 15514505687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7757252843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 15514505687) ^ 7757252843 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 15514505687) ^ 2 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_16462091119 : Nat.Prime 16462091119 := by
  apply lucas_primality 16462091119 (6 : ZMod 16462091119)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (249425623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (249425623, 1)] : List FactorBlock).map factorBlockValue).prod) = 16462091119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_249425623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 16462091119) ^ 8231045559 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16462091119) ^ 5487363706 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16462091119) ^ 1496553738 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16462091119) ^ 66 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_18501466063 : Nat.Prime 18501466063 := by
  apply lucas_primality 18501466063 (3 : ZMod 18501466063)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (347, 1), (8886391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (347, 1), (8886391, 1)] : List FactorBlock).map factorBlockValue).prod) = 18501466063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_347
      · exact prime_oneHundredFortyEightEP_8886391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18501466063) ^ 9250733031 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 18501466063) ^ 6167155354 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 18501466063) ^ 53318346 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 18501466063) ^ 2082 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_19442078969 : Nat.Prime 19442078969 := by
  apply lucas_primality 19442078969 (3 : ZMod 19442078969)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (17, 1), (41, 1), (268211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (17, 1), (41, 1), (268211, 1)] : List FactorBlock).map factorBlockValue).prod) = 19442078969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_41
      · exact prime_oneHundredFortyEightEP_268211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19442078969) ^ 9721039484 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19442078969) ^ 1495544536 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19442078969) ^ 1143651704 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19442078969) ^ 474197048 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19442078969) ^ 72488 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_19653905023 : Nat.Prime 19653905023 := by
  apply lucas_primality 19653905023 (3 : ZMod 19653905023)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (4289, 1), (11399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (4289, 1), (11399, 1)] : List FactorBlock).map factorBlockValue).prod) = 19653905023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_67
      · exact prime_oneHundredFortyEightEP_4289
      · exact prime_oneHundredFortyEightEP_11399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19653905023) ^ 9826952511 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19653905023) ^ 6551301674 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19653905023) ^ 293341866 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19653905023) ^ 4582398 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 19653905023) ^ 1724178 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_20074555847 : Nat.Prime 20074555847 := by
  apply lucas_primality 20074555847 (5 : ZMod 20074555847)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10037277923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10037277923, 1)] : List FactorBlock).map factorBlockValue).prod) = 20074555847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_10037277923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 20074555847) ^ 10037277923 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 20074555847) ^ 2 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_22776090853 : Nat.Prime 22776090853 := by
  apply lucas_primality 22776090853 (2 : ZMod 22776090853)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (26732501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (26732501, 1)] : List FactorBlock).map factorBlockValue).prod) = 22776090853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_71
      · exact prime_oneHundredFortyEightEP_26732501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22776090853) ^ 11388045426 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22776090853) ^ 7592030284 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22776090853) ^ 320790012 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22776090853) ^ 852 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_24050250269 : Nat.Prime 24050250269 := by
  apply lucas_primality 24050250269 (2 : ZMod 24050250269)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (37, 1), (868993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (37, 1), (868993, 1)] : List FactorBlock).map factorBlockValue).prod) = 24050250269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_37
      · exact prime_oneHundredFortyEightEP_868993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24050250269) ^ 12025125134 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24050250269) ^ 2186386388 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24050250269) ^ 1414720604 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24050250269) ^ 650006764 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24050250269) ^ 27676 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_24415247677 : Nat.Prime 24415247677 := by
  apply lucas_primality 24415247677 (5 : ZMod 24415247677)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6791, 1), (299603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6791, 1), (299603, 1)] : List FactorBlock).map factorBlockValue).prod) = 24415247677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_6791
      · exact prime_oneHundredFortyEightEP_299603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24415247677) ^ 12207623838 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 24415247677) ^ 8138415892 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 24415247677) ^ 3595236 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 24415247677) ^ 81492 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_24861478051 : Nat.Prime 24861478051 := by
  apply lucas_primality 24861478051 (2 : ZMod 24861478051)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (89, 1), (151, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (89, 1), (151, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) = 24861478051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_89
      · exact prime_oneHundredFortyEightEP_151
      · exact prime_oneHundredFortyEightEP_4111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24861478051) ^ 12430739025 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24861478051) ^ 8287159350 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24861478051) ^ 4972295610 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24861478051) ^ 279342450 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24861478051) ^ 164645550 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 24861478051) ^ 6047550 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_26089483591 : Nat.Prime 26089483591 := by
  apply lucas_primality 26089483591 (12 : ZMod 26089483591)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (10736413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (10736413, 1)] : List FactorBlock).map factorBlockValue).prod) = 26089483591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_10736413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 26089483591) ^ 13044741795 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (12 : ZMod 26089483591) ^ 8696494530 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (12 : ZMod 26089483591) ^ 5217896718 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (12 : ZMod 26089483591) ^ 2430 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_28464725449 : Nat.Prime 28464725449 := by
  apply lucas_primality 28464725449 (11 : ZMod 28464725449)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (37, 1), (353, 1), (30269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (37, 1), (353, 1), (30269, 1)] : List FactorBlock).map factorBlockValue).prod) = 28464725449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_37
      · exact prime_oneHundredFortyEightEP_353
      · exact prime_oneHundredFortyEightEP_30269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 28464725449) ^ 14232362724 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 28464725449) ^ 9488241816 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 28464725449) ^ 769316904 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 28464725449) ^ 80636616 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 28464725449) ^ 940392 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_33411929623 : Nat.Prime 33411929623 := by
  apply lucas_primality 33411929623 (3 : ZMod 33411929623)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (1283, 1), (54941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (1283, 1), (54941, 1)] : List FactorBlock).map factorBlockValue).prod) = 33411929623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_79
      · exact prime_oneHundredFortyEightEP_1283
      · exact prime_oneHundredFortyEightEP_54941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33411929623) ^ 16705964811 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 33411929623) ^ 11137309874 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 33411929623) ^ 422935818 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 33411929623) ^ 26042034 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 33411929623) ^ 608142 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_37727210827 : Nat.Prime 37727210827 := by
  apply lucas_primality 37727210827 (2 : ZMod 37727210827)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (199, 1), (172663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (199, 1), (172663, 1)] : List FactorBlock).map factorBlockValue).prod) = 37727210827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_61
      · exact prime_oneHundredFortyEightEP_199
      · exact prime_oneHundredFortyEightEP_172663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37727210827) ^ 18863605413 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37727210827) ^ 12575736942 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37727210827) ^ 618478866 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37727210827) ^ 189583974 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 37727210827) ^ 218502 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_38650125629 : Nat.Prime 38650125629 := by
  apply lucas_primality 38650125629 (2 : ZMod 38650125629)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9662531407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9662531407, 1)] : List FactorBlock).map factorBlockValue).prod) = 38650125629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_9662531407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 38650125629) ^ 19325062814 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 38650125629) ^ 4 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_40997507911 : Nat.Prime 40997507911 := by
  apply lucas_primality 40997507911 (6 : ZMod 40997507911)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (239, 1), (1117, 1), (5119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (239, 1), (1117, 1), (5119, 1)] : List FactorBlock).map factorBlockValue).prod) = 40997507911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_239
      · exact prime_oneHundredFortyEightEP_1117
      · exact prime_oneHundredFortyEightEP_5119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 40997507911) ^ 20498753955 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 40997507911) ^ 13665835970 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 40997507911) ^ 8199501582 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 40997507911) ^ 171537690 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 40997507911) ^ 36703230 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 40997507911) ^ 8008890 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_45219337309 : Nat.Prime 45219337309 := by
  apply lucas_primality 45219337309 (2 : ZMod 45219337309)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (641, 1), (1959583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (641, 1), (1959583, 1)] : List FactorBlock).map factorBlockValue).prod) = 45219337309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_641
      · exact prime_oneHundredFortyEightEP_1959583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45219337309) ^ 22609668654 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 45219337309) ^ 15073112436 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 45219337309) ^ 70544988 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 45219337309) ^ 23076 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_50165491813 : Nat.Prime 50165491813 := by
  apply lucas_primality 50165491813 (2 : ZMod 50165491813)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (227, 1), (479, 1), (38447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (227, 1), (479, 1), (38447, 1)] : List FactorBlock).map factorBlockValue).prod) = 50165491813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_227
      · exact prime_oneHundredFortyEightEP_479
      · exact prime_oneHundredFortyEightEP_38447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50165491813) ^ 25082745906 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 50165491813) ^ 16721830604 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 50165491813) ^ 220993356 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 50165491813) ^ 104729628 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 50165491813) ^ 1304796 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_54702140897 : Nat.Prime 54702140897 := by
  apply lucas_primality 54702140897 (3 : ZMod 54702140897)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (23, 1), (397, 1), (14401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (23, 1), (397, 1), (14401, 1)] : List FactorBlock).map factorBlockValue).prod) = 54702140897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_397
      · exact prime_oneHundredFortyEightEP_14401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 54702140897) ^ 27351070448 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 54702140897) ^ 4207856992 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 54702140897) ^ 2378353952 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 54702140897) ^ 137788768 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 54702140897) ^ 3798496 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_55365378889 : Nat.Prime 55365378889 := by
  apply lucas_primality 55365378889 (19 : ZMod 55365378889)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (659, 1), (3500593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (659, 1), (3500593, 1)] : List FactorBlock).map factorBlockValue).prod) = 55365378889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_659
      · exact prime_oneHundredFortyEightEP_3500593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 55365378889) ^ 27682689444 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (19 : ZMod 55365378889) ^ 18455126296 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (19 : ZMod 55365378889) ^ 84014232 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (19 : ZMod 55365378889) ^ 15816 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_62480522899 : Nat.Prime 62480522899 := by
  apply lucas_primality 62480522899 (2 : ZMod 62480522899)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (157, 1), (239, 1), (92507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (157, 1), (239, 1), (92507, 1)] : List FactorBlock).map factorBlockValue).prod) = 62480522899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_157
      · exact prime_oneHundredFortyEightEP_239
      · exact prime_oneHundredFortyEightEP_92507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62480522899) ^ 31240261449 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 62480522899) ^ 20826840966 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 62480522899) ^ 397965114 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 62480522899) ^ 261424782 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 62480522899) ^ 675414 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_68354664589 : Nat.Prime 68354664589 := by
  apply lucas_primality 68354664589 (2 : ZMod 68354664589)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 6), (7, 1), (683, 1), (4903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 6), (7, 1), (683, 1), (4903, 1)] : List FactorBlock).map factorBlockValue).prod) = 68354664589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_683
      · exact prime_oneHundredFortyEightEP_4903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68354664589) ^ 34177332294 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 68354664589) ^ 22784888196 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 68354664589) ^ 9764952084 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 68354664589) ^ 100080036 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 68354664589) ^ 13941396 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_75734237339 : Nat.Prime 75734237339 := by
  apply lucas_primality 75734237339 (2 : ZMod 75734237339)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (518727653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (518727653, 1)] : List FactorBlock).map factorBlockValue).prod) = 75734237339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_73
      · exact prime_oneHundredFortyEightEP_518727653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75734237339) ^ 37867118669 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 75734237339) ^ 1037455306 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 75734237339) ^ 146 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_82752597329 : Nat.Prime 82752597329 := by
  apply lucas_primality 82752597329 (3 : ZMod 82752597329)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (79, 1), (823, 1), (79549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (79, 1), (823, 1), (79549, 1)] : List FactorBlock).map factorBlockValue).prod) = 82752597329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_79
      · exact prime_oneHundredFortyEightEP_823
      · exact prime_oneHundredFortyEightEP_79549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 82752597329) ^ 41376298664 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 82752597329) ^ 1047501232 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 82752597329) ^ 100549936 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 82752597329) ^ 1040272 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_91092127657 : Nat.Prime 91092127657 := by
  apply lucas_primality 91092127657 (7 : ZMod 91092127657)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (521, 1), (1481, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (521, 1), (1481, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod) = 91092127657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_521
      · exact prime_oneHundredFortyEightEP_1481
      · exact prime_oneHundredFortyEightEP_4919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 91092127657) ^ 45546063828 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 91092127657) ^ 30364042552 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 91092127657) ^ 174840936 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 91092127657) ^ 61507176 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 91092127657) ^ 18518424 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_99360319777 : Nat.Prime 99360319777 := by
  apply lucas_primality 99360319777 (5 : ZMod 99360319777)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (37, 1), (27973063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (37, 1), (27973063, 1)] : List FactorBlock).map factorBlockValue).prod) = 99360319777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_37
      · exact prime_oneHundredFortyEightEP_27973063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 99360319777) ^ 49680159888 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 99360319777) ^ 33120106592 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 99360319777) ^ 2685414048 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 99360319777) ^ 3552 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_99411217463 : Nat.Prime 99411217463 := by
  apply lucas_primality 99411217463 (5 : ZMod 99411217463)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (467, 1), (976477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (467, 1), (976477, 1)] : List FactorBlock).map factorBlockValue).prod) = 99411217463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_109
      · exact prime_oneHundredFortyEightEP_467
      · exact prime_oneHundredFortyEightEP_976477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 99411217463) ^ 49705608731 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 99411217463) ^ 912029518 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 99411217463) ^ 212871986 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 99411217463) ^ 101806 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_143014041091 : Nat.Prime 143014041091 := by
  apply lucas_primality 143014041091 (3 : ZMod 143014041091)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (5807, 1), (273643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (5807, 1), (273643, 1)] : List FactorBlock).map factorBlockValue).prod) = 143014041091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_5807
      · exact prime_oneHundredFortyEightEP_273643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 143014041091) ^ 71507020545 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 143014041091) ^ 47671347030 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 143014041091) ^ 28602808218 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 143014041091) ^ 24627870 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 143014041091) ^ 522630 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_167669872789 : Nat.Prime 167669872789 := by
  apply lucas_primality 167669872789 (6 : ZMod 167669872789)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (115475119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (115475119, 1)] : List FactorBlock).map factorBlockValue).prod) = 167669872789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_115475119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 167669872789) ^ 83834936394 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 167669872789) ^ 55889957596 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 167669872789) ^ 15242715708 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 167669872789) ^ 1452 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_173518015637 : Nat.Prime 173518015637 := by
  apply lucas_primality 173518015637 (2 : ZMod 173518015637)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (6197071987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (6197071987, 1)] : List FactorBlock).map factorBlockValue).prod) = 173518015637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_6197071987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 173518015637) ^ 86759007818 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 173518015637) ^ 24788287948 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 173518015637) ^ 28 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_186325664683 : Nat.Prime 186325664683 := by
  apply lucas_primality 186325664683 (5 : ZMod 186325664683)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (439, 1), (7351, 1), (9623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (439, 1), (7351, 1), (9623, 1)] : List FactorBlock).map factorBlockValue).prod) = 186325664683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_439
      · exact prime_oneHundredFortyEightEP_7351
      · exact prime_oneHundredFortyEightEP_9623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 186325664683) ^ 93162832341 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 186325664683) ^ 62108554894 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 186325664683) ^ 424432038 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 186325664683) ^ 25346982 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 186325664683) ^ 19362534 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_200471577739 : Nat.Prime 200471577739 := by
  apply lucas_primality 200471577739 (3 : ZMod 200471577739)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (33411929623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (33411929623, 1)] : List FactorBlock).map factorBlockValue).prod) = 200471577739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_33411929623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 200471577739) ^ 100235788869 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 200471577739) ^ 66823859246 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 200471577739) ^ 6 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_217203079619 : Nat.Prime 217203079619 := by
  apply lucas_primality 217203079619 (2 : ZMod 217203079619)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (15514505687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (15514505687, 1)] : List FactorBlock).map factorBlockValue).prod) = 217203079619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_15514505687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 217203079619) ^ 108601539809 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 217203079619) ^ 31029011374 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 217203079619) ^ 14 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_221461515557 : Nat.Prime 221461515557 := by
  apply lucas_primality 221461515557 (2 : ZMod 221461515557)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (55365378889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (55365378889, 1)] : List FactorBlock).map factorBlockValue).prod) = 221461515557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_55365378889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 221461515557) ^ 110730757778 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 221461515557) ^ 4 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_223794433691 : Nat.Prime 223794433691 := by
  apply lucas_primality 223794433691 (2 : ZMod 223794433691)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (21773, 1), (1027853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (21773, 1), (1027853, 1)] : List FactorBlock).map factorBlockValue).prod) = 223794433691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_21773
      · exact prime_oneHundredFortyEightEP_1027853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 223794433691) ^ 111897216845 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 223794433691) ^ 44758886738 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 223794433691) ^ 10278530 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 223794433691) ^ 217730 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_254482680649 : Nat.Prime 254482680649 := by
  apply lucas_primality 254482680649 (33 : ZMod 254482680649)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (23, 1), (1951, 1), (33757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (23, 1), (1951, 1), (33757, 1)] : List FactorBlock).map factorBlockValue).prod) = 254482680649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_1951
      · exact prime_oneHundredFortyEightEP_33757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 254482680649) ^ 127241340324 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (33 : ZMod 254482680649) ^ 84827560216 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (33 : ZMod 254482680649) ^ 36354668664 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (33 : ZMod 254482680649) ^ 11064464376 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (33 : ZMod 254482680649) ^ 130437048 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (33 : ZMod 254482680649) ^ 7538664 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_260519339351 : Nat.Prime 260519339351 := by
  apply lucas_primality 260519339351 (17 : ZMod 260519339351)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (5210386787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (5210386787, 1)] : List FactorBlock).map factorBlockValue).prod) = 260519339351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_5210386787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 260519339351) ^ 130259669675 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (17 : ZMod 260519339351) ^ 52103867870 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (17 : ZMod 260519339351) ^ 50 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_265648068899 : Nat.Prime 265648068899 := by
  apply lucas_primality 265648068899 (2 : ZMod 265648068899)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (601, 1), (13000297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (601, 1), (13000297, 1)] : List FactorBlock).map factorBlockValue).prod) = 265648068899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_601
      · exact prime_oneHundredFortyEightEP_13000297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 265648068899) ^ 132824034449 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 265648068899) ^ 15626356994 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 265648068899) ^ 442010098 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 265648068899) ^ 20434 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_299483516401 : Nat.Prime 299483516401 := by
  apply lucas_primality 299483516401 (14 : ZMod 299483516401)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (249569597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (249569597, 1)] : List FactorBlock).map factorBlockValue).prod) = 299483516401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_249569597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 299483516401) ^ 149741758200 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (14 : ZMod 299483516401) ^ 99827838800 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (14 : ZMod 299483516401) ^ 59896703280 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (14 : ZMod 299483516401) ^ 1200 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_491990216831 : Nat.Prime 491990216831 := by
  apply lucas_primality 491990216831 (7 : ZMod 491990216831)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 3), (17, 1), (8437493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 3), (17, 1), (8437493, 1)] : List FactorBlock).map factorBlockValue).prod) = 491990216831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_8437493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 491990216831) ^ 245995108415 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 491990216831) ^ 98398043366 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 491990216831) ^ 70284316690 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 491990216831) ^ 28940600990 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 491990216831) ^ 58310 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_584409528191 : Nat.Prime 584409528191 := by
  apply lucas_primality 584409528191 (11 : ZMod 584409528191)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (223, 1), (577, 1), (26717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (223, 1), (577, 1), (26717, 1)] : List FactorBlock).map factorBlockValue).prod) = 584409528191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_223
      · exact prime_oneHundredFortyEightEP_577
      · exact prime_oneHundredFortyEightEP_26717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 584409528191) ^ 292204764095 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 584409528191) ^ 116881905638 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 584409528191) ^ 34377031070 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 584409528191) ^ 2620670530 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 584409528191) ^ 1012841470 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 584409528191) ^ 21874070 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_622228304263 : Nat.Prime 622228304263 := by
  apply lucas_primality 622228304263 (5 : ZMod 622228304263)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (179, 1), (12823, 1), (45181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (179, 1), (12823, 1), (45181, 1)] : List FactorBlock).map factorBlockValue).prod) = 622228304263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_179
      · exact prime_oneHundredFortyEightEP_12823
      · exact prime_oneHundredFortyEightEP_45181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 622228304263) ^ 311114152131 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 622228304263) ^ 207409434754 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 622228304263) ^ 3476135778 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 622228304263) ^ 48524394 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 622228304263) ^ 13771902 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_685995860791 : Nat.Prime 685995860791 := by
  apply lucas_primality 685995860791 (6 : ZMod 685995860791)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (113, 1), (1823051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (113, 1), (1823051, 1)] : List FactorBlock).map factorBlockValue).prod) = 685995860791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_37
      · exact prime_oneHundredFortyEightEP_113
      · exact prime_oneHundredFortyEightEP_1823051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 685995860791) ^ 342997930395 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 685995860791) ^ 228665286930 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 685995860791) ^ 137199172158 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 685995860791) ^ 18540428670 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 685995860791) ^ 6070759830 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 685995860791) ^ 376290 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_830363077751 : Nat.Prime 830363077751 := by
  apply lucas_primality 830363077751 (7 : ZMod 830363077751)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (43, 1), (77243077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (43, 1), (77243077, 1)] : List FactorBlock).map factorBlockValue).prod) = 830363077751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_43
      · exact prime_oneHundredFortyEightEP_77243077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 830363077751) ^ 415181538875 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 830363077751) ^ 166072615550 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 830363077751) ^ 19310769250 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 830363077751) ^ 10750 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1231858315333 : Nat.Prime 1231858315333 := by
  apply lucas_primality 1231858315333 (5 : ZMod 1231858315333)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (61, 1), (439, 1), (1277803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (61, 1), (439, 1), (1277803, 1)] : List FactorBlock).map factorBlockValue).prod) = 1231858315333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_61
      · exact prime_oneHundredFortyEightEP_439
      · exact prime_oneHundredFortyEightEP_1277803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1231858315333) ^ 615929157666 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231858315333) ^ 410619438444 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231858315333) ^ 20194398612 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231858315333) ^ 2806055388 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231858315333) ^ 964044 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1422471478579 : Nat.Prime 1422471478579 := by
  apply lucas_primality 1422471478579 (3 : ZMod 1422471478579)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (36529, 1), (72923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (36529, 1), (72923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1422471478579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_89
      · exact prime_oneHundredFortyEightEP_36529
      · exact prime_oneHundredFortyEightEP_72923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1422471478579) ^ 711235739289 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1422471478579) ^ 474157159526 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1422471478579) ^ 15982825602 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1422471478579) ^ 38940882 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1422471478579) ^ 19506486 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1563116036107 : Nat.Prime 1563116036107 := by
  apply lucas_primality 1563116036107 (2 : ZMod 1563116036107)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (260519339351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (260519339351, 1)] : List FactorBlock).map factorBlockValue).prod) = 1563116036107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_260519339351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1563116036107) ^ 781558018053 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1563116036107) ^ 521038678702 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1563116036107) ^ 6 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1721905917007 : Nat.Prime 1721905917007 := by
  apply lucas_primality 1721905917007 (3 : ZMod 1721905917007)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (26089483591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (26089483591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1721905917007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_26089483591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1721905917007) ^ 860952958503 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1721905917007) ^ 573968639002 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1721905917007) ^ 156536901546 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1721905917007) ^ 66 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1836421967449 : Nat.Prime 1836421967449 := by
  apply lucas_primality 1836421967449 (7 : ZMod 1836421967449)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (3469, 1), (2450837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (3469, 1), (2450837, 1)] : List FactorBlock).map factorBlockValue).prod) = 1836421967449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_3469
      · exact prime_oneHundredFortyEightEP_2450837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1836421967449) ^ 918210983724 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1836421967449) ^ 612140655816 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1836421967449) ^ 529380792 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1836421967449) ^ 749304 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2073859330297 : Nat.Prime 2073859330297 := by
  apply lucas_primality 2073859330297 (5 : ZMod 2073859330297)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 2), (101, 1), (593, 1), (8537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 2), (101, 1), (593, 1), (8537, 1)] : List FactorBlock).map factorBlockValue).prod) = 2073859330297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_101
      · exact prime_oneHundredFortyEightEP_593
      · exact prime_oneHundredFortyEightEP_8537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2073859330297) ^ 1036929665148 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2073859330297) ^ 691286443432 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2073859330297) ^ 159527640792 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2073859330297) ^ 20533260696 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2073859330297) ^ 3497233272 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2073859330297) ^ 242926008 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2528451321943 : Nat.Prime 2528451321943 := by
  apply lucas_primality 2528451321943 (6 : ZMod 2528451321943)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (4630863227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (4630863227, 1)] : List FactorBlock).map factorBlockValue).prod) = 2528451321943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_4630863227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2528451321943) ^ 1264225660971 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2528451321943) ^ 842817107314 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2528451321943) ^ 361207331706 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2528451321943) ^ 194496255534 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 2528451321943) ^ 546 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2602097585887 : Nat.Prime 2602097585887 := by
  apply lucas_primality 2602097585887 (3 : ZMod 2602097585887)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (40241, 1), (10777141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (40241, 1), (10777141, 1)] : List FactorBlock).map factorBlockValue).prod) = 2602097585887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_40241
      · exact prime_oneHundredFortyEightEP_10777141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2602097585887) ^ 1301048792943 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2602097585887) ^ 867365861962 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2602097585887) ^ 64662846 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2602097585887) ^ 241446 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2692763088179 : Nat.Prime 2692763088179 := by
  apply lucas_primality 2692763088179 (2 : ZMod 2692763088179)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (59, 1), (1201054009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (59, 1), (1201054009, 1)] : List FactorBlock).map factorBlockValue).prod) = 2692763088179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_59
      · exact prime_oneHundredFortyEightEP_1201054009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2692763088179) ^ 1346381544089 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2692763088179) ^ 141724373062 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2692763088179) ^ 45640052342 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2692763088179) ^ 2242 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_3066433510013 : Nat.Prime 3066433510013 := by
  apply lucas_primality 3066433510013 (2 : ZMod 3066433510013)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (154667, 1), (4956509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (154667, 1), (4956509, 1)] : List FactorBlock).map factorBlockValue).prod) = 3066433510013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_154667
      · exact prime_oneHundredFortyEightEP_4956509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3066433510013) ^ 1533216755006 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3066433510013) ^ 19826036 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 3066433510013) ^ 618668 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_3340570741799 : Nat.Prime 3340570741799 := by
  apply lucas_primality 3340570741799 (7 : ZMod 3340570741799)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (1321, 1), (17808589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (1321, 1), (17808589, 1)] : List FactorBlock).map factorBlockValue).prod) = 3340570741799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_71
      · exact prime_oneHundredFortyEightEP_1321
      · exact prime_oneHundredFortyEightEP_17808589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3340570741799) ^ 1670285370899 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3340570741799) ^ 47050292138 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3340570741799) ^ 2528819638 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3340570741799) ^ 187582 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_3493681386313 : Nat.Prime 3493681386313 := by
  apply lucas_primality 3493681386313 (5 : ZMod 3493681386313)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (3643, 1), (3073757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (3643, 1), (3073757, 1)] : List FactorBlock).map factorBlockValue).prod) = 3493681386313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_3643
      · exact prime_oneHundredFortyEightEP_3073757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3493681386313) ^ 1746840693156 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3493681386313) ^ 1164560462104 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3493681386313) ^ 268744722024 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3493681386313) ^ 959012184 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 3493681386313) ^ 1136616 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_3957054855791 : Nat.Prime 3957054855791 := by
  apply lucas_primality 3957054855791 (7 : ZMod 3957054855791)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (191, 1), (48180383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (191, 1), (48180383, 1)] : List FactorBlock).map factorBlockValue).prod) = 3957054855791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_43
      · exact prime_oneHundredFortyEightEP_191
      · exact prime_oneHundredFortyEightEP_48180383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3957054855791) ^ 1978527427895 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3957054855791) ^ 791410971158 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3957054855791) ^ 92024531530 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3957054855791) ^ 20717564690 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3957054855791) ^ 82130 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_4016750233037 : Nat.Prime 4016750233037 := by
  apply lucas_primality 4016750233037 (2 : ZMod 4016750233037)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (16462091119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (16462091119, 1)] : List FactorBlock).map factorBlockValue).prod) = 4016750233037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_61
      · exact prime_oneHundredFortyEightEP_16462091119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4016750233037) ^ 2008375116518 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4016750233037) ^ 65848364476 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4016750233037) ^ 244 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_4067551047709 : Nat.Prime 4067551047709 := by
  apply lucas_primality 4067551047709 (2 : ZMod 4067551047709)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1087, 1), (34648123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1087, 1), (34648123, 1)] : List FactorBlock).map factorBlockValue).prod) = 4067551047709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_1087
      · exact prime_oneHundredFortyEightEP_34648123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4067551047709) ^ 2033775523854 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4067551047709) ^ 1355850349236 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4067551047709) ^ 3741997284 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4067551047709) ^ 117396 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_5155122637909 : Nat.Prime 5155122637909 := by
  apply lucas_primality 5155122637909 (2 : ZMod 5155122637909)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (67, 1), (6907, 1), (309437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (67, 1), (6907, 1), (309437, 1)] : List FactorBlock).map factorBlockValue).prod) = 5155122637909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_67
      · exact prime_oneHundredFortyEightEP_6907
      · exact prime_oneHundredFortyEightEP_309437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5155122637909) ^ 2577561318954 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155122637909) ^ 1718374212636 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155122637909) ^ 76942128924 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155122637909) ^ 746362044 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155122637909) ^ 16659684 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_6967549835189 : Nat.Prime 6967549835189 := by
  apply lucas_primality 6967549835189 (2 : ZMod 6967549835189)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (75734237339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (75734237339, 1)] : List FactorBlock).map factorBlockValue).prod) = 6967549835189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_75734237339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6967549835189) ^ 3483774917594 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6967549835189) ^ 302936949356 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6967549835189) ^ 92 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_8924053076347 : Nat.Prime 8924053076347 := by
  apply lucas_primality 8924053076347 (2 : ZMod 8924053076347)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6451, 1), (230559941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6451, 1), (230559941, 1)] : List FactorBlock).map factorBlockValue).prod) = 8924053076347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_6451
      · exact prime_oneHundredFortyEightEP_230559941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8924053076347) ^ 4462026538173 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8924053076347) ^ 2974684358782 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8924053076347) ^ 1383359646 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 8924053076347) ^ 38706 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_9148952371187 : Nat.Prime 9148952371187 := by
  apply lucas_primality 9148952371187 (2 : ZMod 9148952371187)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2803, 1), (1631992931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2803, 1), (1631992931, 1)] : List FactorBlock).map factorBlockValue).prod) = 9148952371187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_2803
      · exact prime_oneHundredFortyEightEP_1631992931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9148952371187) ^ 4574476185593 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9148952371187) ^ 3263985862 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9148952371187) ^ 5606 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_9204132282353 : Nat.Prime 9204132282353 := by
  apply lucas_primality 9204132282353 (3 : ZMod 9204132282353)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (1559, 1), (52713119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (1559, 1), (52713119, 1)] : List FactorBlock).map factorBlockValue).prod) = 9204132282353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_1559
      · exact prime_oneHundredFortyEightEP_52713119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9204132282353) ^ 4602066141176 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9204132282353) ^ 1314876040336 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9204132282353) ^ 5903869328 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9204132282353) ^ 174608 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_9566758866199 : Nat.Prime 9566758866199 := by
  apply lucas_primality 9566758866199 (3 : ZMod 9566758866199)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (695749, 1), (2291717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (695749, 1), (2291717, 1)] : List FactorBlock).map factorBlockValue).prod) = 9566758866199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_695749
      · exact prime_oneHundredFortyEightEP_2291717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9566758866199) ^ 4783379433099 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9566758866199) ^ 3188919622066 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9566758866199) ^ 13750302 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 9566758866199) ^ 4174494 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_9617943585479 : Nat.Prime 9617943585479 := by
  apply lucas_primality 9617943585479 (11 : ZMod 9617943585479)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (887, 1), (8461, 1), (640777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (887, 1), (8461, 1), (640777, 1)] : List FactorBlock).map factorBlockValue).prod) = 9617943585479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_887
      · exact prime_oneHundredFortyEightEP_8461
      · exact prime_oneHundredFortyEightEP_640777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 9617943585479) ^ 4808971792739 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 9617943585479) ^ 10843228394 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 9617943585479) ^ 1136738398 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 9617943585479) ^ 15009814 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_11738725084243 : Nat.Prime 11738725084243 := by
  apply lucas_primality 11738725084243 (2 : ZMod 11738725084243)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (50165491813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (50165491813, 1)] : List FactorBlock).map factorBlockValue).prod) = 11738725084243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_50165491813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11738725084243) ^ 5869362542121 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11738725084243) ^ 3912908361414 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11738725084243) ^ 902978852634 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11738725084243) ^ 234 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_11953009354969 : Nat.Prime 11953009354969 := by
  apply lucas_primality 11953009354969 (13 : ZMod 11953009354969)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (11, 1), (163, 1), (10287787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (11, 1), (163, 1), (10287787, 1)] : List FactorBlock).map factorBlockValue).prod) = 11953009354969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_163
      · exact prime_oneHundredFortyEightEP_10287787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 11953009354969) ^ 5976504677484 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 11953009354969) ^ 3984336451656 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 11953009354969) ^ 1086637214088 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 11953009354969) ^ 73331345736 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 11953009354969) ^ 1161864 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_12443155981783 : Nat.Prime 12443155981783 := by
  apply lucas_primality 12443155981783 (3 : ZMod 12443155981783)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2073859330297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2073859330297, 1)] : List FactorBlock).map factorBlockValue).prod) = 12443155981783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_2073859330297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12443155981783) ^ 6221577990891 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12443155981783) ^ 4147718660594 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 12443155981783) ^ 6 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_12845068878989 : Nat.Prime 12845068878989 := by
  apply lucas_primality 12845068878989 (2 : ZMod 12845068878989)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (33073, 1), (97096339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (33073, 1), (97096339, 1)] : List FactorBlock).map factorBlockValue).prod) = 12845068878989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_33073
      · exact prime_oneHundredFortyEightEP_97096339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12845068878989) ^ 6422534439494 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12845068878989) ^ 388385356 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 12845068878989) ^ 132292 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_14041116385607 : Nat.Prime 14041116385607 := by
  apply lucas_primality 14041116385607 (5 : ZMod 14041116385607)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (3169, 1), (7216241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (3169, 1), (7216241, 1)] : List FactorBlock).map factorBlockValue).prod) = 14041116385607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_307
      · exact prime_oneHundredFortyEightEP_3169
      · exact prime_oneHundredFortyEightEP_7216241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14041116385607) ^ 7020558192803 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 14041116385607) ^ 45736535458 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 14041116385607) ^ 4430771974 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 14041116385607) ^ 1945766 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_14224714785791 : Nat.Prime 14224714785791 := by
  apply lucas_primality 14224714785791 (11 : ZMod 14224714785791)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1422471478579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1422471478579, 1)] : List FactorBlock).map factorBlockValue).prod) = 14224714785791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_1422471478579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 14224714785791) ^ 7112357392895 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 14224714785791) ^ 2844942957158 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 14224714785791) ^ 10 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_17703188661923 : Nat.Prime 17703188661923 := by
  apply lucas_primality 17703188661923 (2 : ZMod 17703188661923)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (409, 1), (120905251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (409, 1), (120905251, 1)] : List FactorBlock).map factorBlockValue).prod) = 17703188661923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_179
      · exact prime_oneHundredFortyEightEP_409
      · exact prime_oneHundredFortyEightEP_120905251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17703188661923) ^ 8851594330961 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17703188661923) ^ 98900495318 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17703188661923) ^ 43284079858 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 17703188661923) ^ 146422 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_18293785381727 : Nat.Prime 18293785381727 := by
  apply lucas_primality 18293785381727 (5 : ZMod 18293785381727)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (271, 1), (821, 1), (41111293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (271, 1), (821, 1), (41111293, 1)] : List FactorBlock).map factorBlockValue).prod) = 18293785381727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_271
      · exact prime_oneHundredFortyEightEP_821
      · exact prime_oneHundredFortyEightEP_41111293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18293785381727) ^ 9146892690863 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 18293785381727) ^ 67504743106 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 18293785381727) ^ 22282320806 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 18293785381727) ^ 444982 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_22986283483379 : Nat.Prime 22986283483379 := by
  apply lucas_primality 22986283483379 (2 : ZMod 22986283483379)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (59, 1), (97, 1), (113, 1), (461, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (59, 1), (97, 1), (113, 1), (461, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) = 22986283483379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_59
      · exact prime_oneHundredFortyEightEP_97
      · exact prime_oneHundredFortyEightEP_113
      · exact prime_oneHundredFortyEightEP_461
      · exact prime_oneHundredFortyEightEP_2029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22986283483379) ^ 11493141741689 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 1209804393862 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 389598025142 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 236971994674 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 203418437906 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 49861786298 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22986283483379) ^ 11328873082 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_28449429571583 : Nat.Prime 28449429571583 := by
  apply lucas_primality 28449429571583 (5 : ZMod 28449429571583)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14224714785791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14224714785791, 1)] : List FactorBlock).map factorBlockValue).prod) = 28449429571583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_14224714785791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 28449429571583) ^ 14224714785791 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 28449429571583) ^ 2 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_29799899820421 : Nat.Prime 29799899820421 := by
  apply lucas_primality 29799899820421 (7 : ZMod 29799899820421)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (434243, 1), (1143749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (434243, 1), (1143749, 1)] : List FactorBlock).map factorBlockValue).prod) = 29799899820421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_434243
      · exact prime_oneHundredFortyEightEP_1143749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 29799899820421) ^ 14899949910210 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 29799899820421) ^ 9933299940140 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 29799899820421) ^ 5959979964084 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 29799899820421) ^ 68624940 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 29799899820421) ^ 26054580 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_29993286932149 : Nat.Prime 29993286932149 := by
  apply lucas_primality 29993286932149 (2 : ZMod 29993286932149)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (73, 1), (1693, 1), (652381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (73, 1), (1693, 1), (652381, 1)] : List FactorBlock).map factorBlockValue).prod) = 29993286932149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_31
      · exact prime_oneHundredFortyEightEP_73
      · exact prime_oneHundredFortyEightEP_1693
      · exact prime_oneHundredFortyEightEP_652381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29993286932149) ^ 14996643466074 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29993286932149) ^ 9997762310716 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29993286932149) ^ 967525384908 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29993286932149) ^ 410866944276 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29993286932149) ^ 17716058436 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 29993286932149) ^ 45975108 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_30824384266997 : Nat.Prime 30824384266997 := by
  apply lucas_primality 30824384266997 (2 : ZMod 30824384266997)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9767, 1), (788993147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9767, 1), (788993147, 1)] : List FactorBlock).map factorBlockValue).prod) = 30824384266997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_9767
      · exact prime_oneHundredFortyEightEP_788993147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30824384266997) ^ 15412192133498 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30824384266997) ^ 3155972588 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 30824384266997) ^ 39068 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_49772623927133 : Nat.Prime 49772623927133 := by
  apply lucas_primality 49772623927133 (2 : ZMod 49772623927133)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (12443155981783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (12443155981783, 1)] : List FactorBlock).map factorBlockValue).prod) = 49772623927133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_12443155981783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 49772623927133) ^ 24886311963566 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 49772623927133) ^ 4 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_54836194679887 : Nat.Prime 54836194679887 := by
  apply lucas_primality 54836194679887 (3 : ZMod 54836194679887)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (149, 1), (632350777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (149, 1), (632350777, 1)] : List FactorBlock).map factorBlockValue).prod) = 54836194679887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_97
      · exact prime_oneHundredFortyEightEP_149
      · exact prime_oneHundredFortyEightEP_632350777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 54836194679887) ^ 27418097339943 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 54836194679887) ^ 18278731559962 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 54836194679887) ^ 565321594638 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 54836194679887) ^ 368028152214 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 54836194679887) ^ 86718 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_57417555877301 : Nat.Prime 57417555877301 := by
  apply lucas_primality 57417555877301 (2 : ZMod 57417555877301)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (17, 1), (31883, 1), (1059343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (17, 1), (31883, 1), (1059343, 1)] : List FactorBlock).map factorBlockValue).prod) = 57417555877301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_31883
      · exact prime_oneHundredFortyEightEP_1059343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57417555877301) ^ 28708777938650 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 57417555877301) ^ 11483511175460 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 57417555877301) ^ 3377503286900 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 57417555877301) ^ 1800883100 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 57417555877301) ^ 54201100 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_64997993247307 : Nat.Prime 64997993247307 := by
  apply lucas_primality 64997993247307 (3 : ZMod 64997993247307)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (151, 1), (727, 1), (14097409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (151, 1), (727, 1), (14097409, 1)] : List FactorBlock).map factorBlockValue).prod) = 64997993247307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_151
      · exact prime_oneHundredFortyEightEP_727
      · exact prime_oneHundredFortyEightEP_14097409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64997993247307) ^ 32498996623653 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 64997993247307) ^ 21665997749102 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 64997993247307) ^ 9285427606758 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 64997993247307) ^ 430450286406 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 64997993247307) ^ 89405767878 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 64997993247307) ^ 4610634 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_87927484600181 : Nat.Prime 87927484600181 := by
  apply lucas_primality 87927484600181 (3 : ZMod 87927484600181)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (163, 1), (627247001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (163, 1), (627247001, 1)] : List FactorBlock).map factorBlockValue).prod) = 87927484600181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_43
      · exact prime_oneHundredFortyEightEP_163
      · exact prime_oneHundredFortyEightEP_627247001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87927484600181) ^ 43963742300090 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87927484600181) ^ 17585496920036 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87927484600181) ^ 2044825223260 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87927484600181) ^ 539432420860 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87927484600181) ^ 140180 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_114835111754603 : Nat.Prime 114835111754603 := by
  apply lucas_primality 114835111754603 (2 : ZMod 114835111754603)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (57417555877301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (57417555877301, 1)] : List FactorBlock).map factorBlockValue).prod) = 114835111754603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_57417555877301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 114835111754603) ^ 57417555877301 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 114835111754603) ^ 2 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_130869397677047 : Nat.Prime 130869397677047 := by
  apply lucas_primality 130869397677047 (5 : ZMod 130869397677047)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (491990216831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (491990216831, 1)] : List FactorBlock).map factorBlockValue).prod) = 130869397677047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_491990216831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 130869397677047) ^ 65434698838523 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 130869397677047) ^ 18695628239578 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 130869397677047) ^ 6887863035634 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 130869397677047) ^ 266 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_168024026229727 : Nat.Prime 168024026229727 := by
  apply lucas_primality 168024026229727 (5 : ZMod 168024026229727)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (952087, 1), (29413283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (952087, 1), (29413283, 1)] : List FactorBlock).map factorBlockValue).prod) = 168024026229727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_952087
      · exact prime_oneHundredFortyEightEP_29413283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 168024026229727) ^ 84012013114863 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 168024026229727) ^ 56008008743242 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 168024026229727) ^ 176479698 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 168024026229727) ^ 5712522 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_232566918384727 : Nat.Prime 232566918384727 := by
  apply lucas_primality 232566918384727 (3 : ZMod 232566918384727)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (47, 1), (74731, 1), (159937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (47, 1), (74731, 1), (159937, 1)] : List FactorBlock).map factorBlockValue).prod) = 232566918384727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_47
      · exact prime_oneHundredFortyEightEP_74731
      · exact prime_oneHundredFortyEightEP_159937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 232566918384727) ^ 116283459192363 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 232566918384727) ^ 77522306128242 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 232566918384727) ^ 10111605147162 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 232566918384727) ^ 4948232306058 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 232566918384727) ^ 3112054146 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 232566918384727) ^ 1454115798 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_10789
      · exact prime_oneHundredFortyEightEP_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_419570339988143 : Nat.Prime 419570339988143 := by
  apply lucas_primality 419570339988143 (5 : ZMod 419570339988143)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (47, 1), (91092127657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (47, 1), (91092127657, 1)] : List FactorBlock).map factorBlockValue).prod) = 419570339988143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_47
      · exact prime_oneHundredFortyEightEP_91092127657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 419570339988143) ^ 209785169994071 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 419570339988143) ^ 59938619998306 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 419570339988143) ^ 8927028510386 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 419570339988143) ^ 4606 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_504712688535233 : Nat.Prime 504712688535233 := by
  apply lucas_primality 504712688535233 (3 : ZMod 504712688535233)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (101, 1), (1237, 1), (63120899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (101, 1), (1237, 1), (63120899, 1)] : List FactorBlock).map factorBlockValue).prod) = 504712688535233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_101
      · exact prime_oneHundredFortyEightEP_1237
      · exact prime_oneHundredFortyEightEP_63120899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 504712688535233) ^ 252356344267616 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 504712688535233) ^ 4997155332032 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 504712688535233) ^ 408013491136 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 504712688535233) ^ 7995968 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_557403986815121 : Nat.Prime 557403986815121 := by
  apply lucas_primality 557403986815121 (3 : ZMod 557403986815121)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (6967549835189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (6967549835189, 1)] : List FactorBlock).map factorBlockValue).prod) = 557403986815121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_6967549835189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 557403986815121) ^ 278701993407560 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 557403986815121) ^ 111480797363024 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 557403986815121) ^ 80 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_571123394779433 : Nat.Prime 571123394779433 := by
  apply lucas_primality 571123394779433 (3 : ZMod 571123394779433)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (29, 1), (223794433691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (29, 1), (223794433691, 1)] : List FactorBlock).map factorBlockValue).prod) = 571123394779433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_29
      · exact prime_oneHundredFortyEightEP_223794433691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 571123394779433) ^ 285561697389716 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 571123394779433) ^ 51920308616312 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 571123394779433) ^ 19693910164808 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 571123394779433) ^ 2552 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_575043437281343 : Nat.Prime 575043437281343 := by
  apply lucas_primality 575043437281343 (5 : ZMod 575043437281343)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4588121, 1), (62666551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4588121, 1), (62666551, 1)] : List FactorBlock).map factorBlockValue).prod) = 575043437281343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_4588121
      · exact prime_oneHundredFortyEightEP_62666551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 575043437281343) ^ 287521718640671 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 575043437281343) ^ 125333102 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 575043437281343) ^ 9176242 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_575181047894729 : Nat.Prime 575181047894729 := by
  apply lucas_primality 575181047894729 (3 : ZMod 575181047894729)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19381, 1), (337245151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19381, 1), (337245151, 1)] : List FactorBlock).map factorBlockValue).prod) = 575181047894729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_19381
      · exact prime_oneHundredFortyEightEP_337245151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 575181047894729) ^ 287590523947364 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 575181047894729) ^ 52289186172248 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 575181047894729) ^ 29677573288 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 575181047894729) ^ 1705528 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_668699774255147 : Nat.Prime 668699774255147 := by
  apply lucas_primality 668699774255147 (2 : ZMod 668699774255147)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (203653, 1), (96574273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (203653, 1), (96574273, 1)] : List FactorBlock).map factorBlockValue).prod) = 668699774255147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_203653
      · exact prime_oneHundredFortyEightEP_96574273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 668699774255147) ^ 334349887127573 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 668699774255147) ^ 39335280838538 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 668699774255147) ^ 3283525282 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 668699774255147) ^ 6924202 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_752366243928821 : Nat.Prime 752366243928821 := by
  apply lucas_primality 752366243928821 (2 : ZMod 752366243928821)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (15733, 1), (20563, 1), (116279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (15733, 1), (20563, 1), (116279, 1)] : List FactorBlock).map factorBlockValue).prod) = 752366243928821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_15733
      · exact prime_oneHundredFortyEightEP_20563
      · exact prime_oneHundredFortyEightEP_116279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 752366243928821) ^ 376183121964410 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752366243928821) ^ 150473248785764 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752366243928821) ^ 47820901540 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752366243928821) ^ 36588350140 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 752366243928821) ^ 6470353580 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_891401438756377 : Nat.Prime 891401438756377 := by
  apply lucas_primality 891401438756377 (5 : ZMod 891401438756377)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (19, 1), (217203079619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (19, 1), (217203079619, 1)] : List FactorBlock).map factorBlockValue).prod) = 891401438756377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_217203079619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 891401438756377) ^ 445700719378188 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 891401438756377) ^ 297133812918792 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 891401438756377) ^ 46915865197704 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 891401438756377) ^ 4104 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_931550935747547 : Nat.Prime 931550935747547 := by
  apply lucas_primality 931550935747547 (2 : ZMod 931550935747547)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (2602097585887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (2602097585887, 1)] : List FactorBlock).map factorBlockValue).prod) = 931550935747547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_179
      · exact prime_oneHundredFortyEightEP_2602097585887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 931550935747547) ^ 465775467873773 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 931550935747547) ^ 5204195171774 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 931550935747547) ^ 358 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1114807973630243 : Nat.Prime 1114807973630243 := by
  apply lucas_primality 1114807973630243 (2 : ZMod 1114807973630243)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (557403986815121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (557403986815121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1114807973630243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_557403986815121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1114807973630243) ^ 557403986815121 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1114807973630243) ^ 2 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1159577773171439 : Nat.Prime 1159577773171439 := by
  apply lucas_primality 1159577773171439 (13 : ZMod 1159577773171439)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23747, 1), (24415247677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23747, 1), (24415247677, 1)] : List FactorBlock).map factorBlockValue).prod) = 1159577773171439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_23747
      · exact prime_oneHundredFortyEightEP_24415247677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 1159577773171439) ^ 579788886585719 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 1159577773171439) ^ 48830495354 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 1159577773171439) ^ 47494 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1277534715979789 : Nat.Prime 1277534715979789 := by
  apply lucas_primality 1277534715979789 (2 : ZMod 1277534715979789)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 2), (1373, 1), (175825693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 2), (1373, 1), (175825693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1277534715979789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_1373
      · exact prime_oneHundredFortyEightEP_175825693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1277534715979789) ^ 638767357989894 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277534715979789) ^ 425844905326596 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277534715979789) ^ 182504959425684 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277534715979789) ^ 930469567356 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277534715979789) ^ 7265916 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1943338104961783 : Nat.Prime 1943338104961783 := by
  apply lucas_primality 1943338104961783 (5 : ZMod 1943338104961783)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (751, 1), (9176125001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (751, 1), (9176125001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1943338104961783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_47
      · exact prime_oneHundredFortyEightEP_751
      · exact prime_oneHundredFortyEightEP_9176125001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1943338104961783) ^ 971669052480891 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1943338104961783) ^ 647779368320594 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1943338104961783) ^ 41347619254506 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1943338104961783) ^ 2587667250282 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 1943338104961783) ^ 211782 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2067033008116243 : Nat.Prime 2067033008116243 := by
  apply lucas_primality 2067033008116243 (2 : ZMod 2067033008116243)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (149, 1), (24861478051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (149, 1), (24861478051, 1)] : List FactorBlock).map factorBlockValue).prod) = 2067033008116243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_31
      · exact prime_oneHundredFortyEightEP_149
      · exact prime_oneHundredFortyEightEP_24861478051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2067033008116243) ^ 1033516504058121 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2067033008116243) ^ 689011002705414 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2067033008116243) ^ 66678484132782 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2067033008116243) ^ 13872704752458 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2067033008116243) ^ 83142 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2219577909681289 : Nat.Prime 2219577909681289 := by
  apply lucas_primality 2219577909681289 (7 : ZMod 2219577909681289)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (1907, 1), (6917, 1), (539321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (1907, 1), (6917, 1), (539321, 1)] : List FactorBlock).map factorBlockValue).prod) = 2219577909681289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_1907
      · exact prime_oneHundredFortyEightEP_6917
      · exact prime_oneHundredFortyEightEP_539321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2219577909681289) ^ 1109788954840644 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2219577909681289) ^ 739859303227096 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2219577909681289) ^ 170736762283176 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2219577909681289) ^ 1163910807384 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2219577909681289) ^ 320887365864 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2219577909681289) ^ 4115504328 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2916911028175211 : Nat.Prime 2916911028175211 := by
  apply lucas_primality 2916911028175211 (2 : ZMod 2916911028175211)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (18911, 1), (1402219501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (18911, 1), (1402219501, 1)] : List FactorBlock).map factorBlockValue).prod) = 2916911028175211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_18911
      · exact prime_oneHundredFortyEightEP_1402219501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2916911028175211) ^ 1458455514087605 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2916911028175211) ^ 583382205635042 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2916911028175211) ^ 265173729834110 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2916911028175211) ^ 154244145110 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2916911028175211) ^ 2080210 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_3127319457225839 : Nat.Prime 3127319457225839 := by
  apply lucas_primality 3127319457225839 (7 : ZMod 3127319457225839)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (359, 1), (622228304263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (359, 1), (622228304263, 1)] : List FactorBlock).map factorBlockValue).prod) = 3127319457225839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_359
      · exact prime_oneHundredFortyEightEP_622228304263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3127319457225839) ^ 1563659728612919 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3127319457225839) ^ 446759922460834 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3127319457225839) ^ 8711196259682 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 3127319457225839) ^ 5026 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_4233315837530443 : Nat.Prime 4233315837530443 := by
  apply lucas_primality 4233315837530443 (2 : ZMod 4233315837530443)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (157, 1), (569, 1), (17333, 1), (35051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (157, 1), (569, 1), (17333, 1), (35051, 1)] : List FactorBlock).map factorBlockValue).prod) = 4233315837530443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_157
      · exact prime_oneHundredFortyEightEP_569
      · exact prime_oneHundredFortyEightEP_17333
      · exact prime_oneHundredFortyEightEP_35051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4233315837530443) ^ 2116657918765221 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4233315837530443) ^ 1411105279176814 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4233315837530443) ^ 325639679810034 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4233315837530443) ^ 26963795143506 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4233315837530443) ^ 7439922385818 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4233315837530443) ^ 244234456674 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4233315837530443) ^ 120775893342 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_4950325821875611 : Nat.Prime 4950325821875611 := by
  apply lucas_primality 4950325821875611 (2 : ZMod 4950325821875611)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (839, 1), (3989, 1), (4482227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (839, 1), (3989, 1), (4482227, 1)] : List FactorBlock).map factorBlockValue).prod) = 4950325821875611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_839
      · exact prime_oneHundredFortyEightEP_3989
      · exact prime_oneHundredFortyEightEP_4482227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4950325821875611) ^ 2475162910937805 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4950325821875611) ^ 1650108607291870 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4950325821875611) ^ 990065164375122 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4950325821875611) ^ 450029620170510 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4950325821875611) ^ 5900269155990 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4950325821875611) ^ 1240994189490 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 4950325821875611) ^ 1104434430 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_9810302457188581 : Nat.Prime 9810302457188581 := by
  apply lucas_primality 9810302457188581 (6 : ZMod 9810302457188581)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (9617943585479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (9617943585479, 1)] : List FactorBlock).map factorBlockValue).prod) = 9810302457188581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_9617943585479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9810302457188581) ^ 4905151228594290 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 9810302457188581) ^ 3270100819062860 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 9810302457188581) ^ 1962060491437716 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 9810302457188581) ^ 577076615128740 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 9810302457188581) ^ 1020 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_11410627178559493 : Nat.Prime 11410627178559493 := by
  apply lucas_primality 11410627178559493 (2 : ZMod 11410627178559493)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (17, 1), (29, 1), (107, 1), (462203219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (17, 1), (29, 1), (107, 1), (462203219, 1)] : List FactorBlock).map factorBlockValue).prod) = 11410627178559493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_29
      · exact prime_oneHundredFortyEightEP_107
      · exact prime_oneHundredFortyEightEP_462203219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11410627178559493) ^ 5705313589279746 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11410627178559493) ^ 3803542392853164 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11410627178559493) ^ 877740552196884 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11410627178559493) ^ 671213363444676 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11410627178559493) ^ 393469902708948 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11410627178559493) ^ 106641375500556 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 11410627178559493) ^ 24687468 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_15575693869264381 : Nat.Prime 15575693869264381 := by
  apply lucas_primality 15575693869264381 (2 : ZMod 15575693869264381)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (3137, 1), (82752597329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (3137, 1), (82752597329, 1)] : List FactorBlock).map factorBlockValue).prod) = 15575693869264381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_3137
      · exact prime_oneHundredFortyEightEP_82752597329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15575693869264381) ^ 7787846934632190 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15575693869264381) ^ 5191897956421460 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15575693869264381) ^ 3115138773852876 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15575693869264381) ^ 4965155839740 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 15575693869264381) ^ 188220 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_16536256092662833 : Nat.Prime 16536256092662833 := by
  apply lucas_primality 16536256092662833 (5 : ZMod 16536256092662833)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (114835111754603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (114835111754603, 1)] : List FactorBlock).map factorBlockValue).prod) = 16536256092662833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_114835111754603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 16536256092662833) ^ 8268128046331416 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 16536256092662833) ^ 5512085364220944 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 16536256092662833) ^ 144 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_22629149753988059 : Nat.Prime 22629149753988059 := by
  apply lucas_primality 22629149753988059 (2 : ZMod 22629149753988059)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6103847, 1), (1853679307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6103847, 1), (1853679307, 1)] : List FactorBlock).map factorBlockValue).prod) = 22629149753988059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_6103847
      · exact prime_oneHundredFortyEightEP_1853679307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22629149753988059) ^ 11314574876994029 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22629149753988059) ^ 3707358614 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 22629149753988059) ^ 12207694 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_22965055844998711 : Nat.Prime 22965055844998711 := by
  apply lucas_primality 22965055844998711 (11 : ZMod 22965055844998711)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (26893, 1), (28464725449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (26893, 1), (28464725449, 1)] : List FactorBlock).map factorBlockValue).prod) = 22965055844998711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_26893
      · exact prime_oneHundredFortyEightEP_28464725449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 22965055844998711) ^ 11482527922499355 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 22965055844998711) ^ 7655018614999570 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 22965055844998711) ^ 4593011168999742 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 22965055844998711) ^ 853941763470 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 22965055844998711) ^ 806790 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_26169823839032213 : Nat.Prime 26169823839032213 := by
  apply lucas_primality 26169823839032213 (2 : ZMod 26169823839032213)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (89, 1), (4349, 1), (6299, 1), (141233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (89, 1), (4349, 1), (6299, 1), (141233, 1)] : List FactorBlock).map factorBlockValue).prod) = 26169823839032213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_89
      · exact prime_oneHundredFortyEightEP_4349
      · exact prime_oneHundredFortyEightEP_6299
      · exact prime_oneHundredFortyEightEP_141233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26169823839032213) ^ 13084911919516106 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 26169823839032213) ^ 1377359149422748 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 26169823839032213) ^ 294042964483508 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 26169823839032213) ^ 6017434775588 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 26169823839032213) ^ 4154599752188 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 26169823839032213) ^ 185295390164 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_36378828185434153 : Nat.Prime 36378828185434153 := by
  apply lucas_primality 36378828185434153 (5 : ZMod 36378828185434153)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (1523, 1), (95603, 1), (946397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (1523, 1), (95603, 1), (946397, 1)] : List FactorBlock).map factorBlockValue).prod) = 36378828185434153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_1523
      · exact prime_oneHundredFortyEightEP_95603
      · exact prime_oneHundredFortyEightEP_946397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36378828185434153) ^ 18189414092717076 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 36378828185434153) ^ 12126276061811384 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 36378828185434153) ^ 3307166198675832 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 36378828185434153) ^ 23886295591224 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 36378828185434153) ^ 380519734584 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 36378828185434153) ^ 38439289416 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_45190839053075717 : Nat.Prime 45190839053075717 := by
  apply lucas_primality 45190839053075717 (2 : ZMod 45190839053075717)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (13, 1), (47, 1), (3559, 1), (67473073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (13, 1), (47, 1), (3559, 1), (67473073, 1)] : List FactorBlock).map factorBlockValue).prod) = 45190839053075717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_47
      · exact prime_oneHundredFortyEightEP_3559
      · exact prime_oneHundredFortyEightEP_67473073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45190839053075717) ^ 22595419526537858 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 45190839053075717) ^ 6455834150439388 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 45190839053075717) ^ 4108258095734156 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 45190839053075717) ^ 3476218388698132 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 45190839053075717) ^ 961507213895228 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 45190839053075717) ^ 12697622661724 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 45190839053075717) ^ 669761092 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_49362491128819369 : Nat.Prime 49362491128819369 := by
  apply lucas_primality 49362491128819369 (11 : ZMod 49362491128819369)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (433, 1), (5231, 1), (908057209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (433, 1), (5231, 1), (908057209, 1)] : List FactorBlock).map factorBlockValue).prod) = 49362491128819369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_433
      · exact prime_oneHundredFortyEightEP_5231
      · exact prime_oneHundredFortyEightEP_908057209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 49362491128819369) ^ 24681245564409684 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 49362491128819369) ^ 16454163709606456 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 49362491128819369) ^ 114001134246696 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 49362491128819369) ^ 9436530515928 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (11 : ZMod 49362491128819369) ^ 54360552 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_129256456234098229 : Nat.Prime 129256456234098229 := by
  apply lucas_primality 129256456234098229 (6 : ZMod 129256456234098229)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (19, 1), (137, 1), (6917, 1), (12209081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (19, 1), (137, 1), (6917, 1), (12209081, 1)] : List FactorBlock).map factorBlockValue).prod) = 129256456234098229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_137
      · exact prime_oneHundredFortyEightEP_6917
      · exact prime_oneHundredFortyEightEP_12209081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 129256456234098229) ^ 64628228117049114 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 129256456234098229) ^ 43085485411366076 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 129256456234098229) ^ 18465208033442604 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 129256456234098229) ^ 6802971380742012 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 129256456234098229) ^ 943477782730644 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 129256456234098229) ^ 18686779851684 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 129256456234098229) ^ 10586911188 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_150913139871667717 : Nat.Prime 150913139871667717 := by
  apply lucas_primality 150913139871667717 (2 : ZMod 150913139871667717)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (647161, 1), (719730169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (647161, 1), (719730169, 1)] : List FactorBlock).map factorBlockValue).prod) = 150913139871667717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_647161
      · exact prime_oneHundredFortyEightEP_719730169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 150913139871667717) ^ 75456569935833858 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 150913139871667717) ^ 50304379957222572 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 150913139871667717) ^ 233192574756 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 150913139871667717) ^ 209680164 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_168914146405805347 : Nat.Prime 168914146405805347 := by
  apply lucas_primality 168914146405805347 (2 : ZMod 168914146405805347)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (30181, 1), (10250375021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (30181, 1), (10250375021, 1)] : List FactorBlock).map factorBlockValue).prod) = 168914146405805347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_30181
      · exact prime_oneHundredFortyEightEP_10250375021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 168914146405805347) ^ 84457073202902673 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 168914146405805347) ^ 56304715468601782 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 168914146405805347) ^ 24130592343686478 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 168914146405805347) ^ 12993395877369642 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 168914146405805347) ^ 5596704761466 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 168914146405805347) ^ 16478826 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_197449964515277477 : Nat.Prime 197449964515277477 := by
  apply lucas_primality 197449964515277477 (2 : ZMod 197449964515277477)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (49362491128819369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (49362491128819369, 1)] : List FactorBlock).map factorBlockValue).prod) = 197449964515277477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_49362491128819369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 197449964515277477) ^ 98724982257638738 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 197449964515277477) ^ 4 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_450939750378356903 : Nat.Prime 450939750378356903 := by
  apply lucas_primality 450939750378356903 (5 : ZMod 450939750378356903)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (157, 1), (167, 1), (21149, 1), (31278017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (157, 1), (167, 1), (21149, 1), (31278017, 1)] : List FactorBlock).map factorBlockValue).prod) = 450939750378356903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_157
      · exact prime_oneHundredFortyEightEP_167
      · exact prime_oneHundredFortyEightEP_21149
      · exact prime_oneHundredFortyEightEP_31278017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 450939750378356903) ^ 225469875189178451 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 450939750378356903) ^ 34687673106027454 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 450939750378356903) ^ 2872227709416286 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 450939750378356903) ^ 2700238026217706 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 450939750378356903) ^ 21322036520798 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 450939750378356903) ^ 14417146406 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_604005656150070457 : Nat.Prime 604005656150070457 := by
  apply lucas_primality 604005656150070457 (10 : ZMod 604005656150070457)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (9041, 1), (36017, 1), (3360299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (9041, 1), (36017, 1), (3360299, 1)] : List FactorBlock).map factorBlockValue).prod) = 604005656150070457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_23
      · exact prime_oneHundredFortyEightEP_9041
      · exact prime_oneHundredFortyEightEP_36017
      · exact prime_oneHundredFortyEightEP_3360299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 604005656150070457) ^ 302002828075035228 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (10 : ZMod 604005656150070457) ^ 201335218716690152 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (10 : ZMod 604005656150070457) ^ 26261115484785672 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (10 : ZMod 604005656150070457) ^ 66807394773816 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (10 : ZMod 604005656150070457) ^ 16770015718968 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (10 : ZMod 604005656150070457) ^ 179747592744 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_715259550695108693 : Nat.Prime 715259550695108693 := by
  apply lucas_primality 715259550695108693 (2 : ZMod 715259550695108693)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 2), (569, 1), (265648068899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 2), (569, 1), (265648068899, 1)] : List FactorBlock).map factorBlockValue).prod) = 715259550695108693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_569
      · exact prime_oneHundredFortyEightEP_265648068899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 715259550695108693) ^ 357629775347554346 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 715259550695108693) ^ 102179935813586956 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 715259550695108693) ^ 55019965438085284 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 715259550695108693) ^ 1257046662030068 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 715259550695108693) ^ 2692508 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1211232473956683613 : Nat.Prime 1211232473956683613 := by
  apply lucas_primality 1211232473956683613 (2 : ZMod 1211232473956683613)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (43, 1), (174259, 1), (641450713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (43, 1), (174259, 1), (641450713, 1)] : List FactorBlock).map factorBlockValue).prod) = 1211232473956683613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_43
      · exact prime_oneHundredFortyEightEP_174259
      · exact prime_oneHundredFortyEightEP_641450713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1211232473956683613) ^ 605616236978341806 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211232473956683613) ^ 403744157985561204 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211232473956683613) ^ 173033210565240516 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211232473956683613) ^ 28168197068760084 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211232473956683613) ^ 6950759926068 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211232473956683613) ^ 1888270524 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1713771062559759773 : Nat.Prime 1713771062559759773 := by
  apply lucas_primality 1713771062559759773 (2 : ZMod 1713771062559759773)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (3127319457225839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (3127319457225839, 1)] : List FactorBlock).map factorBlockValue).prod) = 1713771062559759773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_137
      · exact prime_oneHundredFortyEightEP_3127319457225839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1713771062559759773) ^ 856885531279879886 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1713771062559759773) ^ 12509277828903356 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1713771062559759773) ^ 548 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1789440595906773373 : Nat.Prime 1789440595906773373 := by
  apply lucas_primality 1789440595906773373 (2 : ZMod 1789440595906773373)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (223, 1), (668699774255147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (223, 1), (668699774255147, 1)] : List FactorBlock).map factorBlockValue).prod) = 1789440595906773373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_223
      · exact prime_oneHundredFortyEightEP_668699774255147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1789440595906773373) ^ 894720297953386686 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789440595906773373) ^ 596480198635591124 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789440595906773373) ^ 8024397291061764 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789440595906773373) ^ 2676 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_101
      · exact prime_oneHundredFortyEightEP_191
      · exact prime_oneHundredFortyEightEP_48017
      · exact prime_oneHundredFortyEightEP_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2365500069006151261 : Nat.Prime 2365500069006151261 := by
  apply lucas_primality 2365500069006151261 (2 : ZMod 2365500069006151261)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (131, 1), (17703188661923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (131, 1), (17703188661923, 1)] : List FactorBlock).map factorBlockValue).prod) = 2365500069006151261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_131
      · exact prime_oneHundredFortyEightEP_17703188661923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2365500069006151261) ^ 1182750034503075630 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2365500069006151261) ^ 788500023002050420 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2365500069006151261) ^ 473100013801230252 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2365500069006151261) ^ 139147062882714780 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2365500069006151261) ^ 18057252435161460 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 2365500069006151261) ^ 133620 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2619275629351259017 : Nat.Prime 2619275629351259017 := by
  apply lucas_primality 2619275629351259017 (5 : ZMod 2619275629351259017)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (36378828185434153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (36378828185434153, 1)] : List FactorBlock).map factorBlockValue).prod) = 2619275629351259017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_36378828185434153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2619275629351259017) ^ 1309637814675629508 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2619275629351259017) ^ 873091876450419672 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 2619275629351259017) ^ 72 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_5870779669568188091 : Nat.Prime 5870779669568188091 := by
  apply lucas_primality 5870779669568188091 (2 : ZMod 5870779669568188091)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (37965701, 1), (377155549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (37965701, 1), (377155549, 1)] : List FactorBlock).map factorBlockValue).prod) = 5870779669568188091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_41
      · exact prime_oneHundredFortyEightEP_37965701
      · exact prime_oneHundredFortyEightEP_377155549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5870779669568188091) ^ 2935389834784094045 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5870779669568188091) ^ 1174155933913637618 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5870779669568188091) ^ 143189748038248490 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5870779669568188091) ^ 154633775090 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5870779669568188091) ^ 15565937410 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_8140578791553424999 : Nat.Prime 8140578791553424999 := by
  apply lucas_primality 8140578791553424999 (6 : ZMod 8140578791553424999)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (127, 1), (1339411, 1), (2658674663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (127, 1), (1339411, 1), (2658674663, 1)] : List FactorBlock).map factorBlockValue).prod) = 8140578791553424999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_127
      · exact prime_oneHundredFortyEightEP_1339411
      · exact prime_oneHundredFortyEightEP_2658674663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8140578791553424999) ^ 4070289395776712499 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 8140578791553424999) ^ 2713526263851141666 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 8140578791553424999) ^ 64099045602782874 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 8140578791553424999) ^ 6077730279618 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 8140578791553424999) ^ 3061893546 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_8547053746535491097 : Nat.Prime 8547053746535491097 := by
  apply lucas_primality 8547053746535491097 (3 : ZMod 8547053746535491097)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (239, 1), (3697, 1), (9941, 1), (1336619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (239, 1), (3697, 1), (9941, 1), (1336619, 1)] : List FactorBlock).map factorBlockValue).prod) = 8547053746535491097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_239
      · exact prime_oneHundredFortyEightEP_3697
      · exact prime_oneHundredFortyEightEP_9941
      · exact prime_oneHundredFortyEightEP_1336619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8547053746535491097) ^ 4273526873267745548 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8547053746535491097) ^ 1221007678076498728 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8547053746535491097) ^ 657465672810422392 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8547053746535491097) ^ 35761731157052264 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8547053746535491097) ^ 2311889030710168 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8547053746535491097) ^ 859778065238456 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 8547053746535491097) ^ 6394532582984 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_9347691976911383813 : Nat.Prime 9347691976911383813 := by
  apply lucas_primality 9347691976911383813 (2 : ZMod 9347691976911383813)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (211, 1), (6894161, 1), (12263353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (211, 1), (6894161, 1), (12263353, 1)] : List FactorBlock).map factorBlockValue).prod) = 9347691976911383813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_131
      · exact prime_oneHundredFortyEightEP_211
      · exact prime_oneHundredFortyEightEP_6894161
      · exact prime_oneHundredFortyEightEP_12263353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9347691976911383813) ^ 4673845988455691906 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9347691976911383813) ^ 71356427304667052 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9347691976911383813) ^ 44301857710480492 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9347691976911383813) ^ 1355885361092 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 9347691976911383813) ^ 762246016804 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_10477102517405036069 : Nat.Prime 10477102517405036069 := by
  apply lucas_primality 10477102517405036069 (2 : ZMod 10477102517405036069)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2619275629351259017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2619275629351259017, 1)] : List FactorBlock).map factorBlockValue).prod) = 10477102517405036069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_2619275629351259017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 10477102517405036069) ^ 5238551258702518034 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 10477102517405036069) ^ 4 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_14582414203834964759 : Nat.Prime 14582414203834964759 := by
  apply lucas_primality 14582414203834964759 (17 : ZMod 14582414203834964759)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1823911, 1), (1865119, 1), (2143331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1823911, 1), (1865119, 1), (2143331, 1)] : List FactorBlock).map factorBlockValue).prod) = 14582414203834964759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_1823911
      · exact prime_oneHundredFortyEightEP_1865119
      · exact prime_oneHundredFortyEightEP_2143331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 14582414203834964759) ^ 7291207101917482379 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (17 : ZMod 14582414203834964759) ^ 7995134742778 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (17 : ZMod 14582414203834964759) ^ 7818489975082 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (17 : ZMod 14582414203834964759) ^ 6803622120818 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_46590393394217823809 : Nat.Prime 46590393394217823809 := by
  apply lucas_primality 46590393394217823809 (3 : ZMod 46590393394217823809)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (17, 2), (103, 1), (3493681386313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (17, 2), (103, 1), (3493681386313, 1)] : List FactorBlock).map factorBlockValue).prod) = 46590393394217823809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_103
      · exact prime_oneHundredFortyEightEP_3493681386313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46590393394217823809) ^ 23295196697108911904 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46590393394217823809) ^ 6655770484888260544 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46590393394217823809) ^ 2740611376130460224 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46590393394217823809) ^ 452333916448716736 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 46590393394217823809) ^ 13335616 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_116390476548685083427 : Nat.Prime 116390476548685083427 := by
  apply lucas_primality 116390476548685083427 (3 : ZMod 116390476548685083427)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (337, 1), (23629, 1), (221461515557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (337, 1), (23629, 1), (221461515557, 1)] : List FactorBlock).map factorBlockValue).prod) = 116390476548685083427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_337
      · exact prime_oneHundredFortyEightEP_23629
      · exact prime_oneHundredFortyEightEP_221461515557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 116390476548685083427) ^ 58195238274342541713 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 116390476548685083427) ^ 38796825516228361142 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 116390476548685083427) ^ 10580952413516825766 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 116390476548685083427) ^ 345372333972359298 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 116390476548685083427) ^ 4925747029018794 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 116390476548685083427) ^ 525556218 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_154536888817040220149 : Nat.Prime 154536888817040220149 := by
  apply lucas_primality 154536888817040220149 (2 : ZMod 154536888817040220149)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (84913, 1), (64997993247307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (84913, 1), (64997993247307, 1)] : List FactorBlock).map factorBlockValue).prod) = 154536888817040220149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_84913
      · exact prime_oneHundredFortyEightEP_64997993247307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 154536888817040220149) ^ 77268444408520110074 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 154536888817040220149) ^ 22076698402434317164 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 154536888817040220149) ^ 1819943810924596 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 154536888817040220149) ^ 2377564 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_172292429333921453941 : Nat.Prime 172292429333921453941 := by
  apply lucas_primality 172292429333921453941 (7 : ZMod 172292429333921453941)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (168914146405805347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (168914146405805347, 1)] : List FactorBlock).map factorBlockValue).prod) = 172292429333921453941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_168914146405805347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 172292429333921453941) ^ 86146214666960726970 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 172292429333921453941) ^ 57430809777973817980 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 172292429333921453941) ^ 34458485866784290788 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 172292429333921453941) ^ 10134848784348320820 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 172292429333921453941) ^ 1020 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_233708306012414121437 : Nat.Prime 233708306012414121437 := by
  apply lucas_primality 233708306012414121437 (2 : ZMod 233708306012414121437)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (587, 1), (757, 1), (1901191, 1), (69159911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (587, 1), (757, 1), (1901191, 1), (69159911, 1)] : List FactorBlock).map factorBlockValue).prod) = 233708306012414121437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_587
      · exact prime_oneHundredFortyEightEP_757
      · exact prime_oneHundredFortyEightEP_1901191
      · exact prime_oneHundredFortyEightEP_69159911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 233708306012414121437) ^ 116854153006207060718 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 233708306012414121437) ^ 398140214671915028 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 233708306012414121437) ^ 308729598431194348 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 233708306012414121437) ^ 122927315568196 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 233708306012414121437) ^ 3379245326276 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_726114122709561931823 : Nat.Prime 726114122709561931823 := by
  apply lucas_primality 726114122709561931823 (5 : ZMod 726114122709561931823)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2269, 1), (6961, 1), (22986283483379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2269, 1), (6961, 1), (22986283483379, 1)] : List FactorBlock).map factorBlockValue).prod) = 726114122709561931823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_2269
      · exact prime_oneHundredFortyEightEP_6961
      · exact prime_oneHundredFortyEightEP_22986283483379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 726114122709561931823) ^ 363057061354780965911 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 726114122709561931823) ^ 320015038655602438 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 726114122709561931823) ^ 104311754447573902 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 726114122709561931823) ^ 31589018 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2475808933822544132899 : Nat.Prime 2475808933822544132899 := by
  apply lucas_primality 2475808933822544132899 (7 : ZMod 2475808933822544132899)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (127, 1), (421, 1), (563, 1), (173518015637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (127, 1), (421, 1), (563, 1), (173518015637, 1)] : List FactorBlock).map factorBlockValue).prod) = 2475808933822544132899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_79
      · exact prime_oneHundredFortyEightEP_127
      · exact prime_oneHundredFortyEightEP_421
      · exact prime_oneHundredFortyEightEP_563
      · exact prime_oneHundredFortyEightEP_173518015637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2475808933822544132899) ^ 1237904466911272066449 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2475808933822544132899) ^ 825269644607514710966 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2475808933822544132899) ^ 31339353592690432062 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2475808933822544132899) ^ 19494558534035780574 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2475808933822544132899) ^ 5880781315492978938 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2475808933822544132899) ^ 4397529189738089046 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 2475808933822544132899) ^ 14268310554 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_7716691730928192623939 : Nat.Prime 7716691730928192623939 := by
  apply lucas_primality 7716691730928192623939 (2 : ZMod 7716691730928192623939)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (479, 1), (1945301, 1), (40997507911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (479, 1), (1945301, 1), (40997507911, 1)] : List FactorBlock).map factorBlockValue).prod) = 7716691730928192623939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_101
      · exact prime_oneHundredFortyEightEP_479
      · exact prime_oneHundredFortyEightEP_1945301
      · exact prime_oneHundredFortyEightEP_40997507911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7716691730928192623939) ^ 3858345865464096311969 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7716691730928192623939) ^ 76402888425031610138 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7716691730928192623939) ^ 16110003613628794622 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7716691730928192623939) ^ 3966836870452538 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7716691730928192623939) ^ 188223434158 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_13310704921604771534387 : Nat.Prime 13310704921604771534387 := by
  apply lucas_primality 13310704921604771534387 (2 : ZMod 13310704921604771534387)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 3), (149, 1), (15677479, 1), (1296816439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 3), (149, 1), (15677479, 1), (1296816439, 1)] : List FactorBlock).map factorBlockValue).prod) = 13310704921604771534387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_149
      · exact prime_oneHundredFortyEightEP_15677479
      · exact prime_oneHundredFortyEightEP_1296816439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13310704921604771534387) ^ 6655352460802385767193 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13310704921604771534387) ^ 1023900378584982425722 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13310704921604771534387) ^ 89333590077884372714 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13310704921604771534387) ^ 849033503511934 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 13310704921604771534387) ^ 10264139566174 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_24746825576811568437479 : Nat.Prime 24746825576811568437479 := by
  apply lucas_primality 24746825576811568437479 (19 : ZMod 24746825576811568437479)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (277287511, 1), (299483516401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (277287511, 1), (299483516401, 1)] : List FactorBlock).map factorBlockValue).prod) = 24746825576811568437479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_149
      · exact prime_oneHundredFortyEightEP_277287511
      · exact prime_oneHundredFortyEightEP_299483516401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 24746825576811568437479) ^ 12373412788405784218739 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (19 : ZMod 24746825576811568437479) ^ 166086077696721935822 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (19 : ZMod 24746825576811568437479) ^ 89246087887498 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (19 : ZMod 24746825576811568437479) ^ 82631678278 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_25145270029354778201557 : Nat.Prime 25145270029354778201557 := by
  apply lucas_primality 25145270029354778201557 (2 : ZMod 25145270029354778201557)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (697713433, 1), (143014041091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (697713433, 1), (143014041091, 1)] : List FactorBlock).map factorBlockValue).prod) = 25145270029354778201557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_697713433
      · exact prime_oneHundredFortyEightEP_143014041091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25145270029354778201557) ^ 12572635014677389100778 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25145270029354778201557) ^ 8381756676451592733852 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25145270029354778201557) ^ 3592181432764968314508 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25145270029354778201557) ^ 36039538354932 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 25145270029354778201557) ^ 175823785116 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_61023567409695219327329 : Nat.Prime 61023567409695219327329 := by
  apply lucas_primality 61023567409695219327329 (3 : ZMod 61023567409695219327329)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (930426883, 1), (186325664683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (930426883, 1), (186325664683, 1)] : List FactorBlock).map factorBlockValue).prod) = 61023567409695219327329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_930426883
      · exact prime_oneHundredFortyEightEP_186325664683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 61023567409695219327329) ^ 30511783704847609663664 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 61023567409695219327329) ^ 5547597037245019938848 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 61023567409695219327329) ^ 65586633968416 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 61023567409695219327329) ^ 327510262816 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_76579866411664230037727 : Nat.Prime 76579866411664230037727 := by
  apply lucas_primality 76579866411664230037727 (5 : ZMod 76579866411664230037727)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (199, 1), (269, 1), (971, 1), (1013, 1), (19653905023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (199, 1), (269, 1), (971, 1), (1013, 1), (19653905023, 1)] : List FactorBlock).map factorBlockValue).prod) = 76579866411664230037727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_37
      · exact prime_oneHundredFortyEightEP_199
      · exact prime_oneHundredFortyEightEP_269
      · exact prime_oneHundredFortyEightEP_971
      · exact prime_oneHundredFortyEightEP_1013
      · exact prime_oneHundredFortyEightEP_19653905023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 76579866411664230037727) ^ 38289933205832115018863 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 2069726119234168379398 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 384823449304845377074 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 284683518258974832854 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 78867009692754098906 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 75597104058898548902 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 76579866411664230037727) ^ 3896419888162 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_108267805956440373379271 : Nat.Prime 108267805956440373379271 := by
  apply lucas_primality 108267805956440373379271 (7 : ZMod 108267805956440373379271)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (811, 1), (3323561, 1), (4016750233037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (811, 1), (3323561, 1), (4016750233037, 1)] : List FactorBlock).map factorBlockValue).prod) = 108267805956440373379271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_811
      · exact prime_oneHundredFortyEightEP_3323561
      · exact prime_oneHundredFortyEightEP_4016750233037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 108267805956440373379271) ^ 54133902978220186689635 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 108267805956440373379271) ^ 21653561191288074675854 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 108267805956440373379271) ^ 133499144212626847570 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 108267805956440373379271) ^ 32575844389930070 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 108267805956440373379271) ^ 26954079710 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_855161740313168496667733 : Nat.Prime 855161740313168496667733 := by
  apply lucas_primality 855161740313168496667733 (3 : ZMod 855161740313168496667733)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (13, 1), (67, 1), (439, 1), (11410627178559493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (13, 1), (67, 1), (439, 1), (11410627178559493, 1)] : List FactorBlock).map factorBlockValue).prod) = 855161740313168496667733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_67
      · exact prime_oneHundredFortyEightEP_439
      · exact prime_oneHundredFortyEightEP_11410627178559493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 855161740313168496667733) ^ 427580870156584248333866 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 855161740313168496667733) ^ 122165962901881213809676 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 855161740313168496667733) ^ 65781672331782192051364 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 855161740313168496667733) ^ 12763608064375649203996 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 855161740313168496667733) ^ 1947976629414962406988 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 855161740313168496667733) ^ 74944324 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1038707659892658094278481 : Nat.Prime 1038707659892658094278481 := by
  apply lucas_primality 1038707659892658094278481 (7 : ZMod 1038707659892658094278481)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (5483, 1), (34687, 1), (2528451321943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (5483, 1), (34687, 1), (2528451321943, 1)] : List FactorBlock).map factorBlockValue).prod) = 1038707659892658094278481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_5483
      · exact prime_oneHundredFortyEightEP_34687
      · exact prime_oneHundredFortyEightEP_2528451321943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1038707659892658094278481) ^ 519353829946329047139240 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1038707659892658094278481) ^ 346235886630886031426160 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1038707659892658094278481) ^ 207741531978531618855696 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1038707659892658094278481) ^ 189441484569151576560 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1038707659892658094278481) ^ 29945156972141093040 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 1038707659892658094278481) ^ 410807853360 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1277827672474058067301153 : Nat.Prime 1277827672474058067301153 := by
  apply lucas_primality 1277827672474058067301153 (10 : ZMod 1277827672474058067301153)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13310704921604771534387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13310704921604771534387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1277827672474058067301153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_13310704921604771534387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 1277827672474058067301153) ^ 638913836237029033650576 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (10 : ZMod 1277827672474058067301153) ^ 425942557491352689100384 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (10 : ZMod 1277827672474058067301153) ^ 96 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_2261278885062067476598063 : Nat.Prime 2261278885062067476598063 := by
  apply lucas_primality 2261278885062067476598063 (3 : ZMod 2261278885062067476598063)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (2758541, 1), (3878209, 1), (1677540173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (2758541, 1), (3878209, 1), (1677540173, 1)] : List FactorBlock).map factorBlockValue).prod) = 2261278885062067476598063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_2758541
      · exact prime_oneHundredFortyEightEP_3878209
      · exact prime_oneHundredFortyEightEP_1677540173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2261278885062067476598063) ^ 1130639442531033738299031 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2261278885062067476598063) ^ 753759628354022492199354 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2261278885062067476598063) ^ 323039840723152496656866 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2261278885062067476598063) ^ 819737275995559782 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2261278885062067476598063) ^ 583072981642316718 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 2261278885062067476598063) ^ 1347973015166694 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_5111310689896232269204613 : Nat.Prime 5111310689896232269204613 := by
  apply lucas_primality 5111310689896232269204613 (2 : ZMod 5111310689896232269204613)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1277827672474058067301153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1277827672474058067301153, 1)] : List FactorBlock).map factorBlockValue).prod) = 5111310689896232269204613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_1277827672474058067301153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5111310689896232269204613) ^ 2555655344948116134602306 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 5111310689896232269204613) ^ 4 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_7578962136579794658105493 : Nat.Prime 7578962136579794658105493 := by
  apply lucas_primality 7578962136579794658105493 (2 : ZMod 7578962136579794658105493)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (4363, 1), (69340759, 1), (99411217463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (4363, 1), (69340759, 1), (99411217463, 1)] : List FactorBlock).map factorBlockValue).prod) = 7578962136579794658105493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_4363
      · exact prime_oneHundredFortyEightEP_69340759
      · exact prime_oneHundredFortyEightEP_99411217463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7578962136579794658105493) ^ 3789481068289897329052746 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7578962136579794658105493) ^ 2526320712193264886035164 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7578962136579794658105493) ^ 1082708876654256379729356 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7578962136579794658105493) ^ 1737098816543615553084 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7578962136579794658105493) ^ 109300247731349388 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 7578962136579794658105493) ^ 76238500342284 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_7902782116761560872213609 : Nat.Prime 7902782116761560872213609 := by
  apply lucas_primality 7902782116761560872213609 (22 : ZMod 7902782116761560872213609)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (19, 1), (2475808933822544132899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (19, 1), (2475808933822544132899, 1)] : List FactorBlock).map factorBlockValue).prod) = 7902782116761560872213609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_2475808933822544132899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 7902782116761560872213609) ^ 3951391058380780436106804 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (22 : ZMod 7902782116761560872213609) ^ 2634260705587186957404536 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (22 : ZMod 7902782116761560872213609) ^ 1128968873823080124601944 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (22 : ZMod 7902782116761560872213609) ^ 415935900882187414327032 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (22 : ZMod 7902782116761560872213609) ^ 3192 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_16468282244444020637334731 : Nat.Prime 16468282244444020637334731 := by
  apply lucas_primality 16468282244444020637334731 (6 : ZMod 16468282244444020637334731)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (223, 1), (673, 1), (22933069, 1), (68354664589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (223, 1), (673, 1), (22933069, 1), (68354664589, 1)] : List FactorBlock).map factorBlockValue).prod) = 16468282244444020637334731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_223
      · exact prime_oneHundredFortyEightEP_673
      · exact prime_oneHundredFortyEightEP_22933069
      · exact prime_oneHundredFortyEightEP_68354664589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16468282244444020637334731) ^ 8234141122222010318667365 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16468282244444020637334731) ^ 3293656448888804127466946 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16468282244444020637334731) ^ 2352611749206288662476390 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16468282244444020637334731) ^ 73848799302439554427510 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16468282244444020637334731) ^ 24469958758460654736010 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16468282244444020637334731) ^ 718101979479677170 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 16468282244444020637334731) ^ 240924044371570 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_18873422375926838450186767 : Nat.Prime 18873422375926838450186767 := by
  apply lucas_primality 18873422375926838450186767 (6 : ZMod 18873422375926838450186767)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (17053, 1), (1787220067, 1), (2195951413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (17053, 1), (1787220067, 1), (2195951413, 1)] : List FactorBlock).map factorBlockValue).prod) = 18873422375926838450186767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_47
      · exact prime_oneHundredFortyEightEP_17053
      · exact prime_oneHundredFortyEightEP_1787220067
      · exact prime_oneHundredFortyEightEP_2195951413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 18873422375926838450186767) ^ 9436711187963419225093383 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 18873422375926838450186767) ^ 6291140791975612816728922 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 18873422375926838450186767) ^ 401562178211209328727378 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 18873422375926838450186767) ^ 1106750857674710517222 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 18873422375926838450186767) ^ 10560211763740698 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (6 : ZMod 18873422375926838450186767) ^ 8594644792319382 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_35899774076162847614214509 : Nat.Prime 35899774076162847614214509 := by
  apply lucas_primality 35899774076162847614214509 (2 : ZMod 35899774076162847614214509)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (251, 1), (273131, 1), (1317571, 1), (99360319777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (251, 1), (273131, 1), (1317571, 1), (99360319777, 1)] : List FactorBlock).map factorBlockValue).prod) = 35899774076162847614214509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_251
      · exact prime_oneHundredFortyEightEP_273131
      · exact prime_oneHundredFortyEightEP_1317571
      · exact prime_oneHundredFortyEightEP_99360319777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35899774076162847614214509) ^ 17949887038081423807107254 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35899774076162847614214509) ^ 143026988351246404837508 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35899774076162847614214509) ^ 131437932992457273668 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35899774076162847614214509) ^ 27246937035015834148 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 35899774076162847614214509) ^ 361308962740204 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_81007175392230425588741443 : Nat.Prime 81007175392230425588741443 := by
  apply lucas_primality 81007175392230425588741443 (3 : ZMod 81007175392230425588741443)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 4), (283, 1), (419, 1), (9199, 1), (5155122637909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 4), (283, 1), (419, 1), (9199, 1), (5155122637909, 1)] : List FactorBlock).map factorBlockValue).prod) = 81007175392230425588741443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_7
      · exact prime_oneHundredFortyEightEP_283
      · exact prime_oneHundredFortyEightEP_419
      · exact prime_oneHundredFortyEightEP_9199
      · exact prime_oneHundredFortyEightEP_5155122637909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 81007175392230425588741443) ^ 40503587696115212794370721 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 27002391797410141862913814 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 11572453627461489369820206 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 286244436014948500313574 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 193334547475490275868118 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 8806084943171043112158 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 81007175392230425588741443) ^ 15713918190138 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_194417220941353021412979463 : Nat.Prime 194417220941353021412979463 := by
  apply lucas_primality 194417220941353021412979463 (3 : ZMod 194417220941353021412979463)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (54647, 1), (5870779669568188091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (54647, 1), (5870779669568188091, 1)] : List FactorBlock).map factorBlockValue).prod) = 194417220941353021412979463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_101
      · exact prime_oneHundredFortyEightEP_54647
      · exact prime_oneHundredFortyEightEP_5870779669568188091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 194417220941353021412979463) ^ 97208610470676510706489731 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 194417220941353021412979463) ^ 64805740313784340470993154 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 194417220941353021412979463) ^ 1924922979617356647653262 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 194417220941353021412979463) ^ 3557692479758321983146 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 194417220941353021412979463) ^ 33116082 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_452133071956634933518556891 : Nat.Prime 452133071956634933518556891 := by
  apply lucas_primality 452133071956634933518556891 (2 : ZMod 452133071956634933518556891)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (31, 1), (37, 1), (52919, 1), (2515757, 1), (22776090853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (31, 1), (37, 1), (52919, 1), (2515757, 1), (22776090853, 1)] : List FactorBlock).map factorBlockValue).prod) = 452133071956634933518556891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_31
      · exact prime_oneHundredFortyEightEP_37
      · exact prime_oneHundredFortyEightEP_52919
      · exact prime_oneHundredFortyEightEP_2515757
      · exact prime_oneHundredFortyEightEP_22776090853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 452133071956634933518556891) ^ 226066535978317466759278445 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 452133071956634933518556891) ^ 90426614391326986703711378 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 452133071956634933518556891) ^ 34779467073587302578350530 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 452133071956634933518556891) ^ 14584937805052739790921190 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 452133071956634933518556891) ^ 12219812755584727932933970 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 452133071956634933518556891) ^ 8543870291514105208310 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 452133071956634933518556891) ^ 179720486500339632770 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 452133071956634933518556891) ^ 19851214805682130 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_475476899041352498020873687 : Nat.Prime 475476899041352498020873687 := by
  apply lucas_primality 475476899041352498020873687 (5 : ZMod 475476899041352498020873687)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1951, 1), (9901, 1), (24917, 1), (18293785381727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1951, 1), (9901, 1), (24917, 1), (18293785381727, 1)] : List FactorBlock).map factorBlockValue).prod) = 475476899041352498020873687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_1951
      · exact prime_oneHundredFortyEightEP_9901
      · exact prime_oneHundredFortyEightEP_24917
      · exact prime_oneHundredFortyEightEP_18293785381727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 475476899041352498020873687) ^ 237738449520676249010436843 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 475476899041352498020873687) ^ 158492299680450832673624562 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 475476899041352498020873687) ^ 243709328058099691450986 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 475476899041352498020873687) ^ 48023118780057822242286 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 475476899041352498020873687) ^ 19082429628019123410558 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 475476899041352498020873687) ^ 25991170723818 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1166503325648118128477876779 : Nat.Prime 1166503325648118128477876779 := by
  apply lucas_primality 1166503325648118128477876779 (2 : ZMod 1166503325648118128477876779)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (194417220941353021412979463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (194417220941353021412979463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1166503325648118128477876779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_194417220941353021412979463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1166503325648118128477876779) ^ 583251662824059064238938389 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1166503325648118128477876779) ^ 388834441882706042825958926 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 1166503325648118128477876779) ^ 6 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_1682456719684785762227706893 : Nat.Prime 1682456719684785762227706893 := by
  apply lucas_primality 1682456719684785762227706893 (3 : ZMod 1682456719684785762227706893)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (16462021, 1), (393024829, 1), (3421583713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (16462021, 1), (393024829, 1), (3421583713, 1)] : List FactorBlock).map factorBlockValue).prod) = 1682456719684785762227706893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_19
      · exact prime_oneHundredFortyEightEP_16462021
      · exact prime_oneHundredFortyEightEP_393024829
      · exact prime_oneHundredFortyEightEP_3421583713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1682456719684785762227706893) ^ 841228359842392881113853446 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682456719684785762227706893) ^ 88550353667620303275142468 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682456719684785762227706893) ^ 102202318882036765852 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682456719684785762227706893) ^ 4280789903186461948 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682456719684785762227706893) ^ 491718707127475084 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_6033637891283369630057983339 : Nat.Prime 6033637891283369630057983339 := by
  apply lucas_primality 6033637891283369630057983339 (2 : ZMod 6033637891283369630057983339)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (729203, 1), (4862353, 1), (9148952371187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (729203, 1), (4862353, 1), (9148952371187, 1)] : List FactorBlock).map factorBlockValue).prod) = 6033637891283369630057983339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_31
      · exact prime_oneHundredFortyEightEP_729203
      · exact prime_oneHundredFortyEightEP_4862353
      · exact prime_oneHundredFortyEightEP_9148952371187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6033637891283369630057983339) ^ 3016818945641684815028991669 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6033637891283369630057983339) ^ 2011212630427789876685994446 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6033637891283369630057983339) ^ 194633480363979665485741398 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6033637891283369630057983339) ^ 8274291097655069480046 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6033637891283369630057983339) ^ 1240888493962361356746 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (2 : ZMod 6033637891283369630057983339) ^ 659489485406574 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_12498249917658408519405822631 : Nat.Prime 12498249917658408519405822631 := by
  apply lucas_primality 12498249917658408519405822631 (7 : ZMod 12498249917658408519405822631)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (584409528191, 1), (54836194679887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (584409528191, 1), (54836194679887, 1)] : List FactorBlock).map factorBlockValue).prod) = 12498249917658408519405822631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_13
      · exact prime_oneHundredFortyEightEP_584409528191
      · exact prime_oneHundredFortyEightEP_54836194679887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12498249917658408519405822631) ^ 6249124958829204259702911315 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 12498249917658408519405822631) ^ 4166083305886136173135274210 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 12498249917658408519405822631) ^ 2499649983531681703881164526 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 12498249917658408519405822631) ^ 961403839819877578415832510 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 12498249917658408519405822631) ^ 21386115925155930 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (7 : ZMod 12498249917658408519405822631) ^ 227919715994490 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_43743874711804429817920379207 : Nat.Prime 43743874711804429817920379207 := by
  apply lucas_primality 43743874711804429817920379207 (5 : ZMod 43743874711804429817920379207)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (3066433510013, 1), (419570339988143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (3066433510013, 1), (419570339988143, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804429817920379207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_17
      · exact prime_oneHundredFortyEightEP_3066433510013
      · exact prime_oneHundredFortyEightEP_419570339988143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 43743874711804429817920379207) ^ 21871937355902214908960189603 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 43743874711804429817920379207) ^ 2573169100694378224583551718 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 43743874711804429817920379207) ^ 14265391559596862 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 43743874711804429817920379207) ^ 104258739340442 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_58325166282405906423893838937 : Nat.Prime 58325166282405906423893838937 := by
  apply lucas_primality 58325166282405906423893838937 (5 : ZMod 58325166282405906423893838937)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (79, 1), (103, 1), (479, 1), (5924987, 1), (9566758866199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (79, 1), (103, 1), (479, 1), (5924987, 1), (9566758866199, 1)] : List FactorBlock).map factorBlockValue).prod) = 58325166282405906423893838937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_79
      · exact prime_oneHundredFortyEightEP_103
      · exact prime_oneHundredFortyEightEP_479
      · exact prime_oneHundredFortyEightEP_5924987
      · exact prime_oneHundredFortyEightEP_9566758866199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 58325166282405906423893838937) ^ 29162583141202953211946919468 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 58325166282405906423893838937) ^ 19441722094135302141297946312 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 58325166282405906423893838937) ^ 5302287843855082402172167176 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 58325166282405906423893838937) ^ 738293244081087423087263784 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 58325166282405906423893838937) ^ 566263750314620450717415912 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 58325166282405906423893838937) ^ 121764439002935086479945384 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 58325166282405906423893838937) ^ 9843931519580702273928 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (5 : ZMod 58325166282405906423893838937) ^ 6096648519957864 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_87487749423608859635840758421 : Nat.Prime 87487749423608859635840758421 := by
  apply lucas_primality 87487749423608859635840758421 (3 : ZMod 87487749423608859635840758421)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4373, 1), (6473, 1), (154536888817040220149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4373, 1), (6473, 1), (154536888817040220149, 1)] : List FactorBlock).map factorBlockValue).prod) = 87487749423608859635840758421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_5
      · exact prime_oneHundredFortyEightEP_4373
      · exact prime_oneHundredFortyEightEP_6473
      · exact prime_oneHundredFortyEightEP_154536888817040220149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87487749423608859635840758421) ^ 43743874711804429817920379210 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87487749423608859635840758421) ^ 17497549884721771927168151684 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87487749423608859635840758421) ^ 20006345626254026900489540 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87487749423608859635840758421) ^ 13515796295938337654231540 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (3 : ZMod 87487749423608859635840758421) ^ 566128580 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyEightEP_174975498847217719271681516809 : Nat.Prime 174975498847217719271681516809 := by
  apply lucas_primality 174975498847217719271681516809 (13 : ZMod 174975498847217719271681516809)
  · rw [← oneHundredFortyEightEPFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (79, 1), (103, 1), (479, 1), (5924987, 1), (9566758866199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (79, 1), (103, 1), (479, 1), (5924987, 1), (9566758866199, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyEightEP_2
      · exact prime_oneHundredFortyEightEP_3
      · exact prime_oneHundredFortyEightEP_11
      · exact prime_oneHundredFortyEightEP_79
      · exact prime_oneHundredFortyEightEP_103
      · exact prime_oneHundredFortyEightEP_479
      · exact prime_oneHundredFortyEightEP_5924987
      · exact prime_oneHundredFortyEightEP_9566758866199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 174975498847217719271681516809) ^ 87487749423608859635840758404 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 174975498847217719271681516809) ^ 58325166282405906423893838936 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 174975498847217719271681516809) ^ 15906863531565247206516501528 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 174975498847217719271681516809) ^ 2214879732243262269261791352 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 174975498847217719271681516809) ^ 1698791250943861352152247736 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 174975498847217719271681516809) ^ 365293317008805259439836152 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 174975498847217719271681516809) ^ 29531794558742106821784 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide
    · change (13 : ZMod 174975498847217719271681516809) ^ 18289945559873592 ≠ 1
      rw [← oneHundredFortyEightEPFastPow_eq_pow]
      decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516800 : Nat.totient 174975498847217719271681516800 = 68098175112098698832388096000 := by
  rw [← show ((([(2, 8), (5, 2), (37, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_37, prime_oneHundredFortyEightEP_171401, prime_oneHundredFortyEightEP_714027719, prime_oneHundredFortyEightEP_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516801 : Nat.totient 174975498847217719271681516801 = 174294994181482972774064692800 := by
  rw [← show ((([(277, 1), (3571, 1), (85577621, 1), (2067033008116243, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_277, prime_oneHundredFortyEightEP_3571, prime_oneHundredFortyEightEP_85577621, prime_oneHundredFortyEightEP_2067033008116243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516802 : Nat.totient 174975498847217719271681516802 = 54497288558366118200335057920 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (31, 1), (729203, 1), (4862353, 1), (9148952371187, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_29, prime_oneHundredFortyEightEP_31, prime_oneHundredFortyEightEP_729203, prime_oneHundredFortyEightEP_4862353, prime_oneHundredFortyEightEP_9148952371187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516803 : Nat.totient 174975498847217719271681516803 = 172363924236529746450819635040 := by
  rw [← show ((([(67, 1), (167669872789, 1), (15575693869264381, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_67, prime_oneHundredFortyEightEP_167669872789, prime_oneHundredFortyEightEP_15575693869264381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516804 : Nat.totient 174975498847217719271681516804 = 87451845126397398521289676800 := by
  rw [← show ((([(2, 2), (2729, 1), (22741, 1), (2769784141, 1), (254482680649, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_2729, prime_oneHundredFortyEightEP_22741, prime_oneHundredFortyEightEP_2769784141, prime_oneHundredFortyEightEP_254482680649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516805 : Nat.totient 174975498847217719271681516805 = 93164100424227935832560230400 := by
  rw [← show ((([(3, 1), (5, 1), (701, 1), (4049, 1), (3544217, 1), (1159577773171439, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_701, prime_oneHundredFortyEightEP_4049, prime_oneHundredFortyEightEP_3544217, prime_oneHundredFortyEightEP_1159577773171439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516806 : Nat.totient 174975498847217719271681516806 = 71042683726180755164993474016 := by
  rw [← show ((([(2, 1), (7, 1), (19, 1), (4358816123, 1), (150913139871667717, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_19, prime_oneHundredFortyEightEP_4358816123, prime_oneHundredFortyEightEP_150913139871667717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516807 : Nat.totient 174975498847217719271681516807 = 151978666600547736119721676800 := by
  rw [← show ((([(13, 1), (17, 1), (4441, 1), (75367, 1), (2365500069006151261, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_13, prime_oneHundredFortyEightEP_17, prime_oneHundredFortyEightEP_4441, prime_oneHundredFortyEightEP_75367, prime_oneHundredFortyEightEP_2365500069006151261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516808 : Nat.totient 174975498847217719271681516808 = 51735192433133750920161768960 := by
  rw [← show ((([(2, 3), (3, 2), (11, 1), (79, 1), (103, 1), (479, 1), (5924987, 1), (9566758866199, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_11, prime_oneHundredFortyEightEP_79, prime_oneHundredFortyEightEP_103, prime_oneHundredFortyEightEP_479, prime_oneHundredFortyEightEP_5924987, prime_oneHundredFortyEightEP_9566758866199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516809 : Nat.totient 174975498847217719271681516809 = 174975498847217719271681516808 := by
  rw [← show ((([(174975498847217719271681516809, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_174975498847217719271681516809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516810 : Nat.totient 174975498847217719271681516810 = 67349287704583119967453440000 := by
  rw [← show ((([(2, 1), (5, 1), (41, 1), (101, 1), (311, 1), (1669, 1), (8140578791553424999, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_41, prime_oneHundredFortyEightEP_101, prime_oneHundredFortyEightEP_311, prime_oneHundredFortyEightEP_1669, prime_oneHundredFortyEightEP_8140578791553424999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516811 : Nat.totient 174975498847217719271681516811 = 116650332564811812847787677872 := by
  rw [← show ((([(3, 1), (58325166282405906423893838937, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_58325166282405906423893838937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516812 : Nat.totient 174975498847217719271681516812 = 86878770153352249333671051264 := by
  rw [← show ((([(2, 2), (197, 1), (577, 1), (6197, 1), (50411887, 1), (1231858315333, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_197, prime_oneHundredFortyEightEP_577, prime_oneHundredFortyEightEP_6197, prime_oneHundredFortyEightEP_50411887, prime_oneHundredFortyEightEP_1231858315333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516813 : Nat.totient 174975498847217719271681516813 = 149976523629640289574595944000 := by
  rw [← show ((([(7, 1), (60589, 1), (4692029851, 1), (87927484600181, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_60589, prime_oneHundredFortyEightEP_4692029851, prime_oneHundredFortyEightEP_87927484600181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516814 : Nat.totient 174975498847217719271681516814 = 58313727727292608344814520832 := by
  rw [← show ((([(2, 1), (3, 1), (5099, 1), (11331744007, 1), (504712688535233, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_5099, prime_oneHundredFortyEightEP_11331744007, prime_oneHundredFortyEightEP_504712688535233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516815 : Nat.totient 174975498847217719271681516815 = 138721506926373114493993900800 := by
  rw [← show ((([(5, 1), (151, 1), (419, 1), (19442078969, 1), (28449429571583, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_151, prime_oneHundredFortyEightEP_419, prime_oneHundredFortyEightEP_19442078969, prime_oneHundredFortyEightEP_28449429571583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516816 : Nat.totient 174975498847217719271681516816 = 83683934231278039651673768736 := by
  rw [← show ((([(2, 4), (23, 1), (475476899041352498020873687, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_23, prime_oneHundredFortyEightEP_475476899041352498020873687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516817 : Nat.totient 174975498847217719271681516817 = 113937534133072003246676336280 := by
  rw [← show ((([(3, 2), (43, 1), (452133071956634933518556891, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_43, prime_oneHundredFortyEightEP_452133071956634933518556891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516818 : Nat.totient 174975498847217719271681516818 = 87487749307218383086404000516 := by
  rw [← show ((([(2, 1), (751674467, 1), (116390476548685083427, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_751674467, prime_oneHundredFortyEightEP_116390476548685083427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516819 : Nat.totient 174975498847217719271681516819 = 157840239835455532752997600000 := by
  rw [← show ((([(11, 1), (137, 1), (2351, 1), (1092851, 1), (45190839053075717, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_11, prime_oneHundredFortyEightEP_137, prime_oneHundredFortyEightEP_2351, prime_oneHundredFortyEightEP_1092851, prime_oneHundredFortyEightEP_45190839053075717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516820 : Nat.totient 174975498847217719271681516820 = 36917907449019454475120263680 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (7, 1), (13, 1), (584409528191, 1), (54836194679887, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_13, prime_oneHundredFortyEightEP_584409528191, prime_oneHundredFortyEightEP_54836194679887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516821 : Nat.totient 174975498847217719271681516821 = 173948623530677137737034695360 := by
  rw [← show ((([(263, 1), (491, 1), (26647, 1), (5698093, 1), (8924053076347, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_263, prime_oneHundredFortyEightEP_491, prime_oneHundredFortyEightEP_26647, prime_oneHundredFortyEightEP_5698093, prime_oneHundredFortyEightEP_8924053076347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516822 : Nat.totient 174975498847217719271681516822 = 86809199985272882448108013600 := by
  rw [← show ((([(2, 1), (131, 1), (8111, 1), (1654287587, 1), (49772623927133, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_131, prime_oneHundredFortyEightEP_8111, prime_oneHundredFortyEightEP_1654287587, prime_oneHundredFortyEightEP_49772623927133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516823 : Nat.totient 174975498847217719271681516823 = 116649427949535725566086542400 := by
  rw [← show ((([(3, 1), (128983, 1), (507282851, 1), (891401438756377, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_128983, prime_oneHundredFortyEightEP_507282851, prime_oneHundredFortyEightEP_891401438756377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516824 : Nat.totient 174975498847217719271681516824 = 82341411222193054433169773056 := by
  rw [← show ((([(2, 3), (17, 1), (3066433510013, 1), (419570339988143, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_17, prime_oneHundredFortyEightEP_3066433510013, prime_oneHundredFortyEightEP_419570339988143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516825 : Nat.totient 174975498847217719271681516825 = 132613004402959052795172010560 := by
  rw [← show ((([(5, 2), (19, 1), (25261213, 1), (14582414203834964759, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_19, prime_oneHundredFortyEightEP_25261213, prime_oneHundredFortyEightEP_14582414203834964759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516826 : Nat.totient 174975498847217719271681516826 = 57984393440591034288557414400 := by
  rw [← show ((([(2, 1), (3, 4), (281, 1), (439, 1), (70439, 1), (161419241, 1), (770057053, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_281, prime_oneHundredFortyEightEP_439, prime_oneHundredFortyEightEP_70439, prime_oneHundredFortyEightEP_161419241, prime_oneHundredFortyEightEP_770057053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516827 : Nat.totient 174975498847217719271681516827 = 149968275346624681254937132224 := by
  rw [← show ((([(7, 2), (24419, 1), (49939, 1), (94999, 1), (30824384266997, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_24419, prime_oneHundredFortyEightEP_49939, prime_oneHundredFortyEightEP_94999, prime_oneHundredFortyEightEP_30824384266997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516828 : Nat.totient 174975498847217719271681516828 = 87487749423608859635840758412 := by
  rw [← show ((([(2, 2), (43743874711804429817920379207, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_43743874711804429817920379207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516829 : Nat.totient 174975498847217719271681516829 = 116640109943432020383249245840 := by
  rw [← show ((([(3, 1), (11411, 1), (5111310689896232269204613, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_11411, prime_oneHundredFortyEightEP_5111310689896232269204613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516830 : Nat.totient 174975498847217719271681516830 = 62731292797930593107158518400 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (71, 1), (24050250269, 1), (931550935747547, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_11, prime_oneHundredFortyEightEP_71, prime_oneHundredFortyEightEP_24050250269, prime_oneHundredFortyEightEP_931550935747547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516831 : Nat.totient 174975498847217719271681516831 = 168941860955934349641623533464 := by
  rw [← show ((([(29, 1), (6033637891283369630057983339, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_29, prime_oneHundredFortyEightEP_6033637891283369630057983339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516832 : Nat.totient 174975498847217719271681516832 = 57363673674749244028929331200 := by
  rw [← show ((([(2, 5), (3, 1), (61, 1), (11909, 1), (109253, 1), (22965055844998711, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_61, prime_oneHundredFortyEightEP_11909, prime_oneHundredFortyEightEP_109253, prime_oneHundredFortyEightEP_22965055844998711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516833 : Nat.totient 174975498847217719271681516833 = 155942887680458981109829785600 := by
  rw [← show ((([(13, 1), (31, 1), (431, 1), (1408417, 1), (715259550695108693, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_13, prime_oneHundredFortyEightEP_31, prime_oneHundredFortyEightEP_431, prime_oneHundredFortyEightEP_1408417, prime_oneHundredFortyEightEP_715259550695108693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516834 : Nat.totient 174975498847217719271681516834 = 74989499505950451116434935780 := by
  rw [← show ((([(2, 1), (7, 1), (12498249917658408519405822631, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_12498249917658408519405822631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516835 : Nat.totient 174975498847217719271681516835 = 93320227903184666027191975680 := by
  rw [← show ((([(3, 2), (5, 1), (2461309, 1), (399233077, 1), (3957054855791, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_2461309, prime_oneHundredFortyEightEP_399233077, prime_oneHundredFortyEightEP_3957054855791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516836 : Nat.totient 174975498847217719271681516836 = 86004879102875720506691607072 := by
  rw [← show ((([(2, 2), (59, 1), (3172423, 1), (233708306012414121437, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_59, prime_oneHundredFortyEightEP_3172423, prime_oneHundredFortyEightEP_233708306012414121437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516837 : Nat.totient 174975498847217719271681516837 = 170223914849491331878773709440 := by
  rw [← show ((([(37, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_37, prime_oneHundredFortyEightEP_7561, prime_oneHundredFortyEightEP_2416168199, prime_oneHundredFortyEightEP_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516838 : Nat.totient 174975498847217719271681516838 = 58318347739234304118476851200 := by
  rw [← show ((([(2, 1), (3, 1), (9257, 1), (118621, 1), (2221861, 1), (11953009354969, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_9257, prime_oneHundredFortyEightEP_118621, prime_oneHundredFortyEightEP_2221861, prime_oneHundredFortyEightEP_11953009354969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516839 : Nat.totient 174975498847217719271681516839 = 165586623510588653568962257920 := by
  rw [← show ((([(23, 1), (97, 1), (3511, 1), (30223, 1), (52639, 1), (14041116385607, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_23, prime_oneHundredFortyEightEP_97, prime_oneHundredFortyEightEP_3511, prime_oneHundredFortyEightEP_30223, prime_oneHundredFortyEightEP_52639, prime_oneHundredFortyEightEP_14041116385607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516840 : Nat.totient 174975498847217719271681516840 = 69963384297939554889219622912 := by
  rw [← show ((([(2, 3), (5, 1), (4373, 1), (6473, 1), (154536888817040220149, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_4373, prime_oneHundredFortyEightEP_6473, prime_oneHundredFortyEightEP_154536888817040220149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516841 : Nat.totient 174975498847217719271681516841 = 85549518148694323233042524160 := by
  rw [← show ((([(3, 1), (7, 1), (11, 1), (17, 1), (20074555847, 1), (2219577909681289, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_11, prime_oneHundredFortyEightEP_17, prime_oneHundredFortyEightEP_20074555847, prime_oneHundredFortyEightEP_2219577909681289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516842 : Nat.totient 174975498847217719271681516842 = 87487749423608859635840758420 := by
  rw [← show ((([(2, 1), (87487749423608859635840758421, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_87487749423608859635840758421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516843 : Nat.totient 174975498847217719271681516843 = 170612720559994577936055638784 := by
  rw [← show ((([(53, 1), (173, 1), (2473, 1), (7716691730928192623939, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_53, prime_oneHundredFortyEightEP_173, prime_oneHundredFortyEightEP_2473, prime_oneHundredFortyEightEP_7716691730928192623939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516844 : Nat.totient 174975498847217719271681516844 = 55250396400492008955022722048 := by
  rw [← show ((([(2, 2), (3, 2), (19, 1), (12277, 1), (105529, 1), (197449964515277477, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_19, prime_oneHundredFortyEightEP_12277, prime_oneHundredFortyEightEP_105529, prime_oneHundredFortyEightEP_197449964515277477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516845 : Nat.totient 174975498847217719271681516845 = 136997465984731876788845461440 := by
  rw [← show ((([(5, 1), (47, 1), (29611, 1), (25145270029354778201557, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_47, prime_oneHundredFortyEightEP_29611, prime_oneHundredFortyEightEP_25145270029354778201557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516846 : Nat.totient 174975498847217719271681516846 = 80757922544751984725493338400 := by
  rw [← show ((([(2, 1), (13, 1), (685995860791, 1), (9810302457188581, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_13, prime_oneHundredFortyEightEP_685995860791, prime_oneHundredFortyEightEP_9810302457188581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516847 : Nat.totient 174975498847217719271681516847 = 116650210517676993457347111680 := by
  rw [← show ((([(3, 1), (955781, 1), (61023567409695219327329, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_955781, prime_oneHundredFortyEightEP_61023567409695219327329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516848 : Nat.totient 174975498847217719271681516848 = 74244673536772211946752827392 := by
  rw [← show ((([(2, 4), (7, 1), (109, 1), (1307, 1), (54702140897, 1), (200471577739, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_109, prime_oneHundredFortyEightEP_1307, prime_oneHundredFortyEightEP_54702140897, prime_oneHundredFortyEightEP_200471577739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516849 : Nat.totient 174975498847217719271681516849 = 174974947495919283483674826480 := by
  rw [← show ((([(317363, 1), (18501466063, 1), (29799899820421, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_317363, prime_oneHundredFortyEightEP_18501466063, prime_oneHundredFortyEightEP_29799899820421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516850 : Nat.totient 174975498847217719271681516850 = 46660133025924725139115071120 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (1166503325648118128477876779, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_1166503325648118128477876779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516851 : Nat.totient 174975498847217719271681516851 = 170707803753331905741391152960 := by
  rw [← show ((([(41, 1), (3340570741799, 1), (1277534715979789, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_41, prime_oneHundredFortyEightEP_3340570741799, prime_oneHundredFortyEightEP_1277534715979789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516852 : Nat.totient 174975498847217719271681516852 = 79532786060498002747980714560 := by
  rw [← show ((([(2, 2), (11, 1), (51929, 1), (76579866411664230037727, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_11, prime_oneHundredFortyEightEP_51929, prime_oneHundredFortyEightEP_76579866411664230037727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516853 : Nat.totient 174975498847217719271681516853 = 116252208562807563460178741568 := by
  rw [← show ((([(3, 3), (293, 1), (1721905917007, 1), (12845068878989, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_293, prime_oneHundredFortyEightEP_1721905917007, prime_oneHundredFortyEightEP_12845068878989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516854 : Nat.totient 174975498847217719271681516854 = 87485648397855531808582485664 := by
  rw [← show ((([(2, 1), (58997, 1), (141539, 1), (10477102517405036069, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_58997, prime_oneHundredFortyEightEP_141539, prime_oneHundredFortyEightEP_10477102517405036069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516855 : Nat.totient 174975498847217719271681516855 = 119958270225683297992033098240 := by
  rw [← show ((([(5, 1), (7, 1), (4813, 1), (1038707659892658094278481, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_4813, prime_oneHundredFortyEightEP_1038707659892658094278481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516856 : Nat.totient 174975498847217719271681516856 = 58324300139958254900906266080 := by
  rw [← show ((([(2, 3), (3, 1), (67339, 1), (108267805956440373379271, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_67339, prime_oneHundredFortyEightEP_108267805956440373379271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516857 : Nat.totient 174975498847217719271681516857 = 171219687794408278420094341152 := by
  rw [← show ((([(73, 1), (127, 1), (18873422375926838450186767, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_73, prime_oneHundredFortyEightEP_127, prime_oneHundredFortyEightEP_18873422375926838450186767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516858 : Nat.totient 174975498847217719271681516858 = 82341055260854670223888116480 := by
  rw [← show ((([(2, 1), (17, 1), (231331, 1), (5469296603, 1), (4067551047709, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_17, prime_oneHundredFortyEightEP_231331, prime_oneHundredFortyEightEP_5469296603, prime_oneHundredFortyEightEP_4067551047709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516859 : Nat.totient 174975498847217719271681516859 = 107555835209173633798423458432 := by
  rw [← show ((([(3, 1), (13, 1), (887, 1), (38650125629, 1), (130869397677047, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_13, prime_oneHundredFortyEightEP_887, prime_oneHundredFortyEightEP_38650125629, prime_oneHundredFortyEightEP_130869397677047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516860 : Nat.totient 174975498847217719271681516860 = 66005192176946643050344733952 := by
  rw [← show ((([(2, 2), (5, 1), (29, 1), (43, 1), (6293333183, 1), (1114807973630243, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_29, prime_oneHundredFortyEightEP_43, prime_oneHundredFortyEightEP_6293333183, prime_oneHundredFortyEightEP_1114807973630243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516861 : Nat.totient 174975498847217719271681516861 = 173427043105142236540499586112 := by
  rw [← show ((([(113, 1), (2692763088179, 1), (575043437281343, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_113, prime_oneHundredFortyEightEP_2692763088179, prime_oneHundredFortyEightEP_575043437281343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516862 : Nat.totient 174975498847217719271681516862 = 47583396917074802656196704512 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (23, 1), (269, 1), (823, 1), (140339, 1), (1943338104961783, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_23, prime_oneHundredFortyEightEP_269, prime_oneHundredFortyEightEP_823, prime_oneHundredFortyEightEP_140339, prime_oneHundredFortyEightEP_1943338104961783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516863 : Nat.totient 174975498847217719271681516863 = 149003381632166478859385623680 := by
  rw [← show ((([(11, 2), (19, 1), (89, 1), (855161740313168496667733, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_11, prime_oneHundredFortyEightEP_19, prime_oneHundredFortyEightEP_89, prime_oneHundredFortyEightEP_855161740313168496667733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516864 : Nat.totient 174975498847217719271681516864 = 84665554984546856642311672320 := by
  rw [← show ((([(2, 6), (31, 1), (9434767, 1), (9347691976911383813, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_31, prime_oneHundredFortyEightEP_9434767, prime_oneHundredFortyEightEP_9347691976911383813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516865 : Nat.totient 174975498847217719271681516865 = 92956799321266044249828311040 := by
  rw [← show ((([(3, 1), (5, 1), (257, 1), (263443, 1), (172292429333921453941, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_257, prime_oneHundredFortyEightEP_263443, prime_oneHundredFortyEightEP_172292429333921453941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516866 : Nat.totient 174975498847217719271681516866 = 87451849649532696788226541488 := by
  rw [← show ((([(2, 1), (2437, 1), (35899774076162847614214509, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_2437, prime_oneHundredFortyEightEP_35899774076162847614214509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516867 : Nat.totient 174975498847217719271681516867 = 174975498847216734338519203320 := by
  rw [← show ((([(232566918384727, 1), (752366243928821, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_232566918384727, prime_oneHundredFortyEightEP_752366243928821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516868 : Nat.totient 174975498847217719271681516868 = 58325166096044332845770672640 := by
  rw [← show ((([(2, 2), (3, 1), (312967771, 1), (46590393394217823809, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_312967771, prime_oneHundredFortyEightEP_46590393394217823809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516869 : Nat.totient 174975498847217719271681516869 = 149931582319200332867636570976 := by
  rw [← show ((([(7, 1), (3163, 1), (7902782116761560872213609, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_3163, prime_oneHundredFortyEightEP_7902782116761560872213609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516870 : Nat.totient 174975498847217719271681516870 = 68604513675916428673512192000 := by
  rw [← show ((([(2, 1), (5, 1), (67, 1), (313, 1), (569, 1), (1765947563, 1), (830363077751, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_67, prime_oneHundredFortyEightEP_313, prime_oneHundredFortyEightEP_569, prime_oneHundredFortyEightEP_1765947563, prime_oneHundredFortyEightEP_830363077751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516871 : Nat.totient 174975498847217719271681516871 = 116648405357446115083268154960 := by
  rw [← show ((([(3, 2), (66791, 1), (645503, 1), (450939750378356903, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_66791, prime_oneHundredFortyEightEP_645503, prime_oneHundredFortyEightEP_450939750378356903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516872 : Nat.totient 174975498847217719271681516872 = 80757922544869716586929930816 := by
  rw [← show ((([(2, 3), (13, 1), (1682456719684785762227706893, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_13, prime_oneHundredFortyEightEP_1682456719684785762227706893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516873 : Nat.totient 174975498847217719271681516873 = 174974214038193431305360035088 := by
  rw [← show ((([(178859, 1), (570839, 1), (1713771062559759773, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_178859, prime_oneHundredFortyEightEP_570839, prime_oneHundredFortyEightEP_1713771062559759773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516874 : Nat.totient 174975498847217719271681516874 = 51477183719686484517305088000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (37, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_11, prime_oneHundredFortyEightEP_37, prime_oneHundredFortyEightEP_461, prime_oneHundredFortyEightEP_69997, prime_oneHundredFortyEightEP_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516875 : Nat.totient 174975498847217719271681516875 = 131746257955552165098677840000 := by
  rw [← show ((([(5, 4), (17, 1), (16468282244444020637334731, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_17, prime_oneHundredFortyEightEP_16468282244444020637334731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516876 : Nat.totient 174975498847217719271681516876 = 74989499505902345449526430528 := by
  rw [← show ((([(2, 2), (7, 2), (1563116036107, 1), (571123394779433, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_1563116036107, prime_oneHundredFortyEightEP_571123394779433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516877 : Nat.totient 174975498847217719271681516877 = 116645810007041688712834430208 := by
  rw [← show ((([(3, 1), (25793, 1), (2261278885062067476598063, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_25793, prime_oneHundredFortyEightEP_2261278885062067476598063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516878 : Nat.totient 174975498847217719271681516878 = 87487749423605912731525651080 := by
  rw [← show ((([(2, 1), (29993286932149, 1), (2916911028175211, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_29993286932149, prime_oneHundredFortyEightEP_2916911028175211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516879 : Nat.totient 174975498847217719271681516879 = 174925602440691216802590228480 := by
  rw [← show ((([(4481, 1), (16127, 1), (263066689, 1), (9204132282353, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_4481, prime_oneHundredFortyEightEP_16127, prime_oneHundredFortyEightEP_263066689, prime_oneHundredFortyEightEP_9204132282353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516880 : Nat.totient 174975498847217719271681516880 = 46660133025924725139115070592 := by
  rw [← show ((([(2, 4), (3, 3), (5, 1), (81007175392230425588741443, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_81007175392230425588741443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516881 : Nat.totient 174975498847217719271681516881 = 172867360207568731935938768592 := by
  rw [← show ((([(83, 1), (1740490439, 1), (1211232473956683613, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_83, prime_oneHundredFortyEightEP_1740490439, prime_oneHundredFortyEightEP_1211232473956683613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516882 : Nat.totient 174975498847217719271681516882 = 82883125007607777618261979008 := by
  rw [← show ((([(2, 1), (19, 1), (14988487, 1), (167287453, 1), (1836421967449, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_19, prime_oneHundredFortyEightEP_14988487, prime_oneHundredFortyEightEP_167287453, prime_oneHundredFortyEightEP_1836421967449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516883 : Nat.totient 174975498847217719271681516883 = 99051307199269942354361164224 := by
  rw [← show ((([(3, 1), (7, 1), (107, 2), (406699, 1), (1789440595906773373, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_107, prime_oneHundredFortyEightEP_406699, prime_oneHundredFortyEightEP_1789440595906773373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516884 : Nat.totient 174975498847217719271681516884 = 87487408537734133909326510240 := by
  rw [← show ((([(2, 2), (267647, 1), (6245311, 1), (26169823839032213, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_267647, prime_oneHundredFortyEightEP_6245311, prime_oneHundredFortyEightEP_26169823839032213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516885 : Nat.totient 174975498847217719271681516885 = 112157126410091028466765593600 := by
  rw [← show ((([(5, 1), (11, 1), (13, 2), (23, 1), (557, 1), (125176811, 1), (11738725084243, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_11, prime_oneHundredFortyEightEP_13, prime_oneHundredFortyEightEP_23, prime_oneHundredFortyEightEP_557, prime_oneHundredFortyEightEP_125176811, prime_oneHundredFortyEightEP_11738725084243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516886 : Nat.totient 174975498847217719271681516886 = 58007907955496973907165888512 := by
  rw [← show ((([(2, 1), (3, 1), (229, 1), (929, 1), (1060529, 1), (129256456234098229, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_229, prime_oneHundredFortyEightEP_929, prime_oneHundredFortyEightEP_1060529, prime_oneHundredFortyEightEP_129256456234098229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516887 : Nat.totient 174975498847217719271681516887 = 171795475677243990891062712384 := by
  rw [← show ((([(79, 1), (179, 1), (546800473, 1), (22629149753988059, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_79, prime_oneHundredFortyEightEP_179, prime_oneHundredFortyEightEP_546800473, prime_oneHundredFortyEightEP_22629149753988059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516888 : Nat.totient 174975498847217719271681516888 = 87034094063369582961265975296 := by
  rw [← show ((([(2, 3), (193, 1), (247997, 1), (12112361333, 1), (37727210827, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_193, prime_oneHundredFortyEightEP_247997, prime_oneHundredFortyEightEP_12112361333, prime_oneHundredFortyEightEP_37727210827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516889 : Nat.totient 174975498847217719271681516889 = 112288292825841817123360521600 := by
  rw [← show ((([(3, 2), (29, 1), (463, 1), (1171, 1), (292091, 1), (4233315837530443, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_29, prime_oneHundredFortyEightEP_463, prime_oneHundredFortyEightEP_1171, prime_oneHundredFortyEightEP_292091, prime_oneHundredFortyEightEP_4233315837530443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516890 : Nat.totient 174975498847217719271681516890 = 59969189275771691420110425600 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (2677, 1), (188624041, 1), (4950325821875611, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_2677, prime_oneHundredFortyEightEP_188624041, prime_oneHundredFortyEightEP_4950325821875611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516891 : Nat.totient 174975498847217719271681516891 = 174967919885081139477023388312 := by
  rw [← show ((([(23087, 1), (7578962136579794658105493, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_23087, prime_oneHundredFortyEightEP_7578962136579794658105493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516892 : Nat.totient 174975498847217719271681516892 = 52330405843250144011911536640 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (41, 1), (47, 1), (613, 1), (726114122709561931823, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_17, prime_oneHundredFortyEightEP_41, prime_oneHundredFortyEightEP_47, prime_oneHundredFortyEightEP_613, prime_oneHundredFortyEightEP_726114122709561931823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516893 : Nat.totient 174975498847217719271681516893 = 172042419011702553528499232640 := by
  rw [← show ((([(61, 1), (2663, 1), (6410691113, 1), (168024026229727, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_61, prime_oneHundredFortyEightEP_2663, prime_oneHundredFortyEightEP_6410691113, prime_oneHundredFortyEightEP_168024026229727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516894 : Nat.totient 174975498847217719271681516894 = 86991607731478402127346050880 := by
  rw [← show ((([(2, 1), (199, 1), (1619, 1), (31771, 1), (8547053746535491097, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_199, prime_oneHundredFortyEightEP_1619, prime_oneHundredFortyEightEP_31771, prime_oneHundredFortyEightEP_8547053746535491097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516895 : Nat.totient 174975498847217719271681516895 = 88779258018356389150522014720 := by
  rw [← show ((([(3, 1), (5, 1), (31, 1), (59, 1), (11088369973, 1), (575181047894729, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_31, prime_oneHundredFortyEightEP_59, prime_oneHundredFortyEightEP_11088369973, prime_oneHundredFortyEightEP_575181047894729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516896 : Nat.totient 174975498847217719271681516896 = 77827776566049310273130810880 := by
  rw [← show ((([(2, 5), (11, 1), (53, 1), (379, 1), (24746825576811568437479, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_11, prime_oneHundredFortyEightEP_53, prime_oneHundredFortyEightEP_379, prime_oneHundredFortyEightEP_24746825576811568437479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516897 : Nat.totient 174975498847217719271681516897 = 149978995975414389844556767440 := by
  rw [← show ((([(7, 1), (49737011, 1), (8043681439, 1), (62480522899, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_7, prime_oneHundredFortyEightEP_49737011, prime_oneHundredFortyEightEP_8043681439, prime_oneHundredFortyEightEP_62480522899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516898 : Nat.totient 174975498847217719271681516898 = 53838615028722530696822610432 := by
  rw [← show ((([(2, 1), (3, 2), (13, 1), (45219337309, 1), (16536256092662833, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_13, prime_oneHundredFortyEightEP_45219337309, prime_oneHundredFortyEightEP_16536256092662833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516899 : Nat.totient 174975498847217719271681516899 = 174769805195078479973527449600 := by
  rw [← show ((([(857, 1), (175141, 1), (512713, 1), (956569, 1), (2376938591, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_857, prime_oneHundredFortyEightEP_175141, prime_oneHundredFortyEightEP_512713, prime_oneHundredFortyEightEP_956569, prime_oneHundredFortyEightEP_2376938591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516900 : Nat.totient 174975498847217719271681516900 = 69840316332600913727232480000 := by
  rw [← show ((([(2, 2), (5, 2), (467, 1), (6203251, 1), (604005656150070457, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_2, prime_oneHundredFortyEightEP_5, prime_oneHundredFortyEightEP_467, prime_oneHundredFortyEightEP_6203251, prime_oneHundredFortyEightEP_604005656150070457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyEightEP_174975498847217719271681516901 : Nat.totient 174975498847217719271681516901 = 108944568255809433500123904000 := by
  rw [← show ((([(3, 1), (19, 2), (71, 1), (21839, 1), (22769, 1), (13432451, 1), (340689277, 1)] : List FactorBlock).map factorBlockValue).prod) = 174975498847217719271681516901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyEightEP_3, prime_oneHundredFortyEightEP_19, prime_oneHundredFortyEightEP_71, prime_oneHundredFortyEightEP_21839, prime_oneHundredFortyEightEP_22769, prime_oneHundredFortyEightEP_13432451, prime_oneHundredFortyEightEP_340689277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFortyEightEP : certifiedKill 1 174975498847217719271681516799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFortyEightEP_174975498847217719271681516800, phi_oneHundredFortyEightEP_174975498847217719271681516801, phi_oneHundredFortyEightEP_174975498847217719271681516802,
    phi_oneHundredFortyEightEP_174975498847217719271681516803, phi_oneHundredFortyEightEP_174975498847217719271681516804, phi_oneHundredFortyEightEP_174975498847217719271681516805,
    phi_oneHundredFortyEightEP_174975498847217719271681516806, phi_oneHundredFortyEightEP_174975498847217719271681516807, phi_oneHundredFortyEightEP_174975498847217719271681516808,
    phi_oneHundredFortyEightEP_174975498847217719271681516809, phi_oneHundredFortyEightEP_174975498847217719271681516810, phi_oneHundredFortyEightEP_174975498847217719271681516811,
    phi_oneHundredFortyEightEP_174975498847217719271681516812, phi_oneHundredFortyEightEP_174975498847217719271681516813, phi_oneHundredFortyEightEP_174975498847217719271681516814,
    phi_oneHundredFortyEightEP_174975498847217719271681516815, phi_oneHundredFortyEightEP_174975498847217719271681516816, phi_oneHundredFortyEightEP_174975498847217719271681516817,
    phi_oneHundredFortyEightEP_174975498847217719271681516818, phi_oneHundredFortyEightEP_174975498847217719271681516819, phi_oneHundredFortyEightEP_174975498847217719271681516820,
    phi_oneHundredFortyEightEP_174975498847217719271681516821, phi_oneHundredFortyEightEP_174975498847217719271681516822, phi_oneHundredFortyEightEP_174975498847217719271681516823,
    phi_oneHundredFortyEightEP_174975498847217719271681516824, phi_oneHundredFortyEightEP_174975498847217719271681516825, phi_oneHundredFortyEightEP_174975498847217719271681516826,
    phi_oneHundredFortyEightEP_174975498847217719271681516827, phi_oneHundredFortyEightEP_174975498847217719271681516828, phi_oneHundredFortyEightEP_174975498847217719271681516829,
    phi_oneHundredFortyEightEP_174975498847217719271681516830, phi_oneHundredFortyEightEP_174975498847217719271681516831, phi_oneHundredFortyEightEP_174975498847217719271681516832,
    phi_oneHundredFortyEightEP_174975498847217719271681516833, phi_oneHundredFortyEightEP_174975498847217719271681516834, phi_oneHundredFortyEightEP_174975498847217719271681516835,
    phi_oneHundredFortyEightEP_174975498847217719271681516836, phi_oneHundredFortyEightEP_174975498847217719271681516837, phi_oneHundredFortyEightEP_174975498847217719271681516838,
    phi_oneHundredFortyEightEP_174975498847217719271681516839, phi_oneHundredFortyEightEP_174975498847217719271681516840, phi_oneHundredFortyEightEP_174975498847217719271681516841,
    phi_oneHundredFortyEightEP_174975498847217719271681516842, phi_oneHundredFortyEightEP_174975498847217719271681516843, phi_oneHundredFortyEightEP_174975498847217719271681516844,
    phi_oneHundredFortyEightEP_174975498847217719271681516845, phi_oneHundredFortyEightEP_174975498847217719271681516846, phi_oneHundredFortyEightEP_174975498847217719271681516847,
    phi_oneHundredFortyEightEP_174975498847217719271681516848, phi_oneHundredFortyEightEP_174975498847217719271681516849, phi_oneHundredFortyEightEP_174975498847217719271681516850,
    phi_oneHundredFortyEightEP_174975498847217719271681516851, phi_oneHundredFortyEightEP_174975498847217719271681516852, phi_oneHundredFortyEightEP_174975498847217719271681516853,
    phi_oneHundredFortyEightEP_174975498847217719271681516854, phi_oneHundredFortyEightEP_174975498847217719271681516855, phi_oneHundredFortyEightEP_174975498847217719271681516856,
    phi_oneHundredFortyEightEP_174975498847217719271681516857, phi_oneHundredFortyEightEP_174975498847217719271681516858, phi_oneHundredFortyEightEP_174975498847217719271681516859,
    phi_oneHundredFortyEightEP_174975498847217719271681516860, phi_oneHundredFortyEightEP_174975498847217719271681516861, phi_oneHundredFortyEightEP_174975498847217719271681516862,
    phi_oneHundredFortyEightEP_174975498847217719271681516863, phi_oneHundredFortyEightEP_174975498847217719271681516864, phi_oneHundredFortyEightEP_174975498847217719271681516865,
    phi_oneHundredFortyEightEP_174975498847217719271681516866, phi_oneHundredFortyEightEP_174975498847217719271681516867, phi_oneHundredFortyEightEP_174975498847217719271681516868,
    phi_oneHundredFortyEightEP_174975498847217719271681516869, phi_oneHundredFortyEightEP_174975498847217719271681516870, phi_oneHundredFortyEightEP_174975498847217719271681516871,
    phi_oneHundredFortyEightEP_174975498847217719271681516872, phi_oneHundredFortyEightEP_174975498847217719271681516873, phi_oneHundredFortyEightEP_174975498847217719271681516874,
    phi_oneHundredFortyEightEP_174975498847217719271681516875, phi_oneHundredFortyEightEP_174975498847217719271681516876, phi_oneHundredFortyEightEP_174975498847217719271681516877,
    phi_oneHundredFortyEightEP_174975498847217719271681516878, phi_oneHundredFortyEightEP_174975498847217719271681516879, phi_oneHundredFortyEightEP_174975498847217719271681516880,
    phi_oneHundredFortyEightEP_174975498847217719271681516881, phi_oneHundredFortyEightEP_174975498847217719271681516882, phi_oneHundredFortyEightEP_174975498847217719271681516883,
    phi_oneHundredFortyEightEP_174975498847217719271681516884, phi_oneHundredFortyEightEP_174975498847217719271681516885, phi_oneHundredFortyEightEP_174975498847217719271681516886,
    phi_oneHundredFortyEightEP_174975498847217719271681516887, phi_oneHundredFortyEightEP_174975498847217719271681516888, phi_oneHundredFortyEightEP_174975498847217719271681516889,
    phi_oneHundredFortyEightEP_174975498847217719271681516890, phi_oneHundredFortyEightEP_174975498847217719271681516891, phi_oneHundredFortyEightEP_174975498847217719271681516892,
    phi_oneHundredFortyEightEP_174975498847217719271681516893, phi_oneHundredFortyEightEP_174975498847217719271681516894, phi_oneHundredFortyEightEP_174975498847217719271681516895,
    phi_oneHundredFortyEightEP_174975498847217719271681516896, phi_oneHundredFortyEightEP_174975498847217719271681516897, phi_oneHundredFortyEightEP_174975498847217719271681516898,
    phi_oneHundredFortyEightEP_174975498847217719271681516899, phi_oneHundredFortyEightEP_174975498847217719271681516900, phi_oneHundredFortyEightEP_174975498847217719271681516901
    ]

end TotientTailPeriodKiller
end Erdos249257
