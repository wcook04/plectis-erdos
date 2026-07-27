import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwentySevenDUFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwentySevenDUFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwentySevenDUFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwentySevenDUFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwentySevenDUFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwentySevenDUFastPow a n * oneHundredTwentySevenDUFastPow a n * a else oneHundredTwentySevenDUFastPow a n * oneHundredTwentySevenDUFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwentySevenDU_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwentySevenDU_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwentySevenDU_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwentySevenDU_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwentySevenDU_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwentySevenDU_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwentySevenDU_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwentySevenDU_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwentySevenDU_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwentySevenDU_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwentySevenDU_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwentySevenDU_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwentySevenDU_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwentySevenDU_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwentySevenDU_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwentySevenDU_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwentySevenDU_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwentySevenDU_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwentySevenDU_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwentySevenDU_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwentySevenDU_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwentySevenDU_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwentySevenDU_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwentySevenDU_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwentySevenDU_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwentySevenDU_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwentySevenDU_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTwentySevenDU_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTwentySevenDU_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwentySevenDU_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwentySevenDU_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwentySevenDU_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTwentySevenDU_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredTwentySevenDU_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwentySevenDU_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredTwentySevenDU_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwentySevenDU_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwentySevenDU_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTwentySevenDU_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwentySevenDU_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTwentySevenDU_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwentySevenDU_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwentySevenDU_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredTwentySevenDU_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwentySevenDU_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTwentySevenDU_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTwentySevenDU_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredTwentySevenDU_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwentySevenDU_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTwentySevenDU_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredTwentySevenDU_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredTwentySevenDU_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredTwentySevenDU_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredTwentySevenDU_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredTwentySevenDU_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredTwentySevenDU_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredTwentySevenDU_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredTwentySevenDU_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredTwentySevenDU_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredTwentySevenDU_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredTwentySevenDU_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredTwentySevenDU_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredTwentySevenDU_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTwentySevenDU_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredTwentySevenDU_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredTwentySevenDU_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredTwentySevenDU_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredTwentySevenDU_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredTwentySevenDU_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredTwentySevenDU_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredTwentySevenDU_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredTwentySevenDU_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredTwentySevenDU_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredTwentySevenDU_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredTwentySevenDU_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredTwentySevenDU_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredTwentySevenDU_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredTwentySevenDU_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredTwentySevenDU_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredTwentySevenDU_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredTwentySevenDU_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredTwentySevenDU_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredTwentySevenDU_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredTwentySevenDU_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredTwentySevenDU_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredTwentySevenDU_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredTwentySevenDU_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredTwentySevenDU_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredTwentySevenDU_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredTwentySevenDU_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredTwentySevenDU_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredTwentySevenDU_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredTwentySevenDU_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredTwentySevenDU_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredTwentySevenDU_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredTwentySevenDU_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredTwentySevenDU_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredTwentySevenDU_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredTwentySevenDU_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredTwentySevenDU_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredTwentySevenDU_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredTwentySevenDU_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1949 : Nat.Prime 1949 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2017 : Nat.Prime 2017 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2467 : Nat.Prime 2467 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2503 : Nat.Prime 2503 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3373 : Nat.Prime 3373 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3571 : Nat.Prime 3571 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3877 : Nat.Prime 3877 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3911 : Nat.Prime 3911 := by norm_num

private theorem prime_oneHundredTwentySevenDU_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_oneHundredTwentySevenDU_4049 : Nat.Prime 4049 := by norm_num

private theorem prime_oneHundredTwentySevenDU_4073 : Nat.Prime 4073 := by norm_num

private theorem prime_oneHundredTwentySevenDU_4129 : Nat.Prime 4129 := by norm_num

private theorem prime_oneHundredTwentySevenDU_4159 : Nat.Prime 4159 := by norm_num

private theorem prime_oneHundredTwentySevenDU_4409 : Nat.Prime 4409 := by norm_num

private theorem prime_oneHundredTwentySevenDU_4451 : Nat.Prime 4451 := by norm_num

private theorem prime_oneHundredTwentySevenDU_5231 : Nat.Prime 5231 := by norm_num

private theorem prime_oneHundredTwentySevenDU_5477 : Nat.Prime 5477 := by norm_num

private theorem prime_oneHundredTwentySevenDU_5563 : Nat.Prime 5563 := by norm_num

private theorem prime_oneHundredTwentySevenDU_5581 : Nat.Prime 5581 := by norm_num

private theorem prime_oneHundredTwentySevenDU_5743 : Nat.Prime 5743 := by norm_num

private theorem prime_oneHundredTwentySevenDU_6961 : Nat.Prime 6961 := by norm_num

private theorem prime_oneHundredTwentySevenDU_6997 : Nat.Prime 6997 := by norm_num

private theorem prime_oneHundredTwentySevenDU_7013 : Nat.Prime 7013 := by norm_num

private theorem prime_oneHundredTwentySevenDU_7283 : Nat.Prime 7283 := by norm_num

private theorem prime_oneHundredTwentySevenDU_7417 : Nat.Prime 7417 := by norm_num

private theorem prime_oneHundredTwentySevenDU_7607 : Nat.Prime 7607 := by norm_num

private theorem prime_oneHundredTwentySevenDU_7699 : Nat.Prime 7699 := by norm_num

private theorem prime_oneHundredTwentySevenDU_7789 : Nat.Prime 7789 := by norm_num

private theorem prime_oneHundredTwentySevenDU_8167 : Nat.Prime 8167 := by norm_num

private theorem prime_oneHundredTwentySevenDU_8209 : Nat.Prime 8209 := by norm_num

private theorem prime_oneHundredTwentySevenDU_8387 : Nat.Prime 8387 := by norm_num

private theorem prime_oneHundredTwentySevenDU_8623 : Nat.Prime 8623 := by norm_num

private theorem prime_oneHundredTwentySevenDU_8641 : Nat.Prime 8641 := by norm_num

private theorem prime_oneHundredTwentySevenDU_8839 : Nat.Prime 8839 := by norm_num

private theorem prime_oneHundredTwentySevenDU_9133 : Nat.Prime 9133 := by norm_num

private theorem prime_oneHundredTwentySevenDU_9157 : Nat.Prime 9157 := by norm_num

private theorem prime_oneHundredTwentySevenDU_9619 : Nat.Prime 9619 := by norm_num

private theorem prime_oneHundredTwentySevenDU_9791 : Nat.Prime 9791 := by norm_num

private theorem prime_oneHundredTwentySevenDU_9833 : Nat.Prime 9833 := by norm_num

private theorem prime_oneHundredTwentySevenDU_9929 : Nat.Prime 9929 := by norm_num

private theorem prime_oneHundredTwentySevenDU_9941 : Nat.Prime 9941 := by norm_num

private theorem prime_oneHundredTwentySevenDU_10289 : Nat.Prime 10289 := by norm_num

private theorem prime_oneHundredTwentySevenDU_10331 : Nat.Prime 10331 := by norm_num

private theorem prime_oneHundredTwentySevenDU_10391 : Nat.Prime 10391 := by norm_num

private theorem prime_oneHundredTwentySevenDU_10427 : Nat.Prime 10427 := by norm_num

private theorem prime_oneHundredTwentySevenDU_10513 : Nat.Prime 10513 := by norm_num

private theorem prime_oneHundredTwentySevenDU_10607 : Nat.Prime 10607 := by norm_num

private theorem prime_oneHundredTwentySevenDU_10831 : Nat.Prime 10831 := by norm_num

private theorem prime_oneHundredTwentySevenDU_10957 : Nat.Prime 10957 := by norm_num

private theorem prime_oneHundredTwentySevenDU_11093 : Nat.Prime 11093 := by norm_num

private theorem prime_oneHundredTwentySevenDU_11471 : Nat.Prime 11471 := by norm_num

private theorem prime_oneHundredTwentySevenDU_12037 : Nat.Prime 12037 := by norm_num

private theorem prime_oneHundredTwentySevenDU_12043 : Nat.Prime 12043 := by norm_num

private theorem prime_oneHundredTwentySevenDU_12739 : Nat.Prime 12739 := by norm_num

private theorem prime_oneHundredTwentySevenDU_12941 : Nat.Prime 12941 := by norm_num

private theorem prime_oneHundredTwentySevenDU_13487 : Nat.Prime 13487 := by norm_num

private theorem prime_oneHundredTwentySevenDU_14387 : Nat.Prime 14387 := by norm_num

private theorem prime_oneHundredTwentySevenDU_14557 : Nat.Prime 14557 := by norm_num

private theorem prime_oneHundredTwentySevenDU_14593 : Nat.Prime 14593 := by norm_num

private theorem prime_oneHundredTwentySevenDU_14653 : Nat.Prime 14653 := by norm_num

private theorem prime_oneHundredTwentySevenDU_15017 : Nat.Prime 15017 := by norm_num

private theorem prime_oneHundredTwentySevenDU_15787 : Nat.Prime 15787 := by norm_num

private theorem prime_oneHundredTwentySevenDU_16001 : Nat.Prime 16001 := by norm_num

private theorem prime_oneHundredTwentySevenDU_16487 : Nat.Prime 16487 := by norm_num

private theorem prime_oneHundredTwentySevenDU_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTwentySevenDU_18223 : Nat.Prime 18223 := by norm_num

private theorem prime_oneHundredTwentySevenDU_20143 : Nat.Prime 20143 := by norm_num

private theorem prime_oneHundredTwentySevenDU_20407 : Nat.Prime 20407 := by norm_num

private theorem prime_oneHundredTwentySevenDU_20717 : Nat.Prime 20717 := by norm_num

private theorem prime_oneHundredTwentySevenDU_20743 : Nat.Prime 20743 := by norm_num

private theorem prime_oneHundredTwentySevenDU_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwentySevenDU_20983 : Nat.Prime 20983 := by norm_num

private theorem prime_oneHundredTwentySevenDU_21347 : Nat.Prime 21347 := by norm_num

private theorem prime_oneHundredTwentySevenDU_21589 : Nat.Prime 21589 := by norm_num

private theorem prime_oneHundredTwentySevenDU_21893 : Nat.Prime 21893 := by norm_num

private theorem prime_oneHundredTwentySevenDU_23039 : Nat.Prime 23039 := by norm_num

private theorem prime_oneHundredTwentySevenDU_23189 : Nat.Prime 23189 := by norm_num

private theorem prime_oneHundredTwentySevenDU_25349 : Nat.Prime 25349 := by norm_num

private theorem prime_oneHundredTwentySevenDU_25589 : Nat.Prime 25589 := by norm_num

private theorem prime_oneHundredTwentySevenDU_27277 : Nat.Prime 27277 := by norm_num

private theorem prime_oneHundredTwentySevenDU_27997 : Nat.Prime 27997 := by norm_num

private theorem prime_oneHundredTwentySevenDU_30859 : Nat.Prime 30859 := by norm_num

private theorem prime_oneHundredTwentySevenDU_30937 : Nat.Prime 30937 := by norm_num

private theorem prime_oneHundredTwentySevenDU_34501 : Nat.Prime 34501 := by norm_num

private theorem prime_oneHundredTwentySevenDU_34763 : Nat.Prime 34763 := by norm_num

private theorem prime_oneHundredTwentySevenDU_36467 : Nat.Prime 36467 := by norm_num

private theorem prime_oneHundredTwentySevenDU_36709 : Nat.Prime 36709 := by norm_num

private theorem prime_oneHundredTwentySevenDU_36713 : Nat.Prime 36713 := by norm_num

private theorem prime_oneHundredTwentySevenDU_39043 : Nat.Prime 39043 := by norm_num

private theorem prime_oneHundredTwentySevenDU_39251 : Nat.Prime 39251 := by norm_num

private theorem prime_oneHundredTwentySevenDU_39511 : Nat.Prime 39511 := by norm_num

private theorem prime_oneHundredTwentySevenDU_41351 : Nat.Prime 41351 := by norm_num

private theorem prime_oneHundredTwentySevenDU_43783 : Nat.Prime 43783 := by norm_num

private theorem prime_oneHundredTwentySevenDU_44111 : Nat.Prime 44111 := by norm_num

private theorem prime_oneHundredTwentySevenDU_45137 : Nat.Prime 45137 := by norm_num

private theorem prime_oneHundredTwentySevenDU_45197 : Nat.Prime 45197 := by norm_num

private theorem prime_oneHundredTwentySevenDU_46171 : Nat.Prime 46171 := by norm_num

private theorem prime_oneHundredTwentySevenDU_46573 : Nat.Prime 46573 := by norm_num

private theorem prime_oneHundredTwentySevenDU_47743 : Nat.Prime 47743 := by norm_num

private theorem prime_oneHundredTwentySevenDU_49333 : Nat.Prime 49333 := by norm_num

private theorem prime_oneHundredTwentySevenDU_50129 : Nat.Prime 50129 := by norm_num

private theorem prime_oneHundredTwentySevenDU_50599 : Nat.Prime 50599 := by norm_num

private theorem prime_oneHundredTwentySevenDU_52571 : Nat.Prime 52571 := by norm_num

private theorem prime_oneHundredTwentySevenDU_52673 : Nat.Prime 52673 := by norm_num

private theorem prime_oneHundredTwentySevenDU_53813 : Nat.Prime 53813 := by norm_num

private theorem prime_oneHundredTwentySevenDU_53819 : Nat.Prime 53819 := by norm_num

private theorem prime_oneHundredTwentySevenDU_53861 : Nat.Prime 53861 := by norm_num

private theorem prime_oneHundredTwentySevenDU_55079 : Nat.Prime 55079 := by norm_num

private theorem prime_oneHundredTwentySevenDU_55339 : Nat.Prime 55339 := by norm_num

private theorem prime_oneHundredTwentySevenDU_56087 : Nat.Prime 56087 := by norm_num

private theorem prime_oneHundredTwentySevenDU_57163 : Nat.Prime 57163 := by norm_num

private theorem prime_oneHundredTwentySevenDU_59453 : Nat.Prime 59453 := by norm_num

private theorem prime_oneHundredTwentySevenDU_59611 : Nat.Prime 59611 := by norm_num

private theorem prime_oneHundredTwentySevenDU_60337 : Nat.Prime 60337 := by norm_num

private theorem prime_oneHundredTwentySevenDU_60383 : Nat.Prime 60383 := by norm_num

private theorem prime_oneHundredTwentySevenDU_63331 : Nat.Prime 63331 := by norm_num

private theorem prime_oneHundredTwentySevenDU_63997 : Nat.Prime 63997 := by norm_num

private theorem prime_oneHundredTwentySevenDU_69911 : Nat.Prime 69911 := by norm_num

private theorem prime_oneHundredTwentySevenDU_71471 : Nat.Prime 71471 := by norm_num

private theorem prime_oneHundredTwentySevenDU_72211 : Nat.Prime 72211 := by norm_num

private theorem prime_oneHundredTwentySevenDU_73387 : Nat.Prime 73387 := by norm_num

private theorem prime_oneHundredTwentySevenDU_78653 : Nat.Prime 78653 := by norm_num

private theorem prime_oneHundredTwentySevenDU_79633 : Nat.Prime 79633 := by norm_num

private theorem prime_oneHundredTwentySevenDU_81569 : Nat.Prime 81569 := by norm_num

private theorem prime_oneHundredTwentySevenDU_82039 : Nat.Prime 82039 := by norm_num

private theorem prime_oneHundredTwentySevenDU_82757 : Nat.Prime 82757 := by norm_num

private theorem prime_oneHundredTwentySevenDU_86269 : Nat.Prime 86269 := by norm_num

private theorem prime_oneHundredTwentySevenDU_107077 : Nat.Prime 107077 := by norm_num

private theorem prime_oneHundredTwentySevenDU_113489 : Nat.Prime 113489 := by norm_num

private theorem prime_oneHundredTwentySevenDU_129457 : Nat.Prime 129457 := by norm_num

private theorem prime_oneHundredTwentySevenDU_129527 : Nat.Prime 129527 := by norm_num

private theorem prime_oneHundredTwentySevenDU_130633 : Nat.Prime 130633 := by norm_num

private theorem prime_oneHundredTwentySevenDU_131687 : Nat.Prime 131687 := by norm_num

private theorem prime_oneHundredTwentySevenDU_135431 : Nat.Prime 135431 := by norm_num

private theorem prime_oneHundredTwentySevenDU_142007 : Nat.Prime 142007 := by norm_num

private theorem prime_oneHundredTwentySevenDU_145661 : Nat.Prime 145661 := by norm_num

private theorem prime_oneHundredTwentySevenDU_147211 : Nat.Prime 147211 := by norm_num

private theorem prime_oneHundredTwentySevenDU_149561 : Nat.Prime 149561 := by norm_num

private theorem prime_oneHundredTwentySevenDU_150473 : Nat.Prime 150473 := by norm_num

private theorem prime_oneHundredTwentySevenDU_151009 : Nat.Prime 151009 := by norm_num

private theorem prime_oneHundredTwentySevenDU_152189 : Nat.Prime 152189 := by norm_num

private theorem prime_oneHundredTwentySevenDU_154487 : Nat.Prime 154487 := by norm_num

private theorem prime_oneHundredTwentySevenDU_157519 : Nat.Prime 157519 := by norm_num

private theorem prime_oneHundredTwentySevenDU_157559 : Nat.Prime 157559 := by norm_num

private theorem prime_oneHundredTwentySevenDU_159707 : Nat.Prime 159707 := by norm_num

private theorem prime_oneHundredTwentySevenDU_165049 : Nat.Prime 165049 := by norm_num

private theorem prime_oneHundredTwentySevenDU_169753 : Nat.Prime 169753 := by norm_num

private theorem prime_oneHundredTwentySevenDU_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTwentySevenDU_173573 : Nat.Prime 173573 := by norm_num

private theorem prime_oneHundredTwentySevenDU_174443 : Nat.Prime 174443 := by norm_num

private theorem prime_oneHundredTwentySevenDU_183167 : Nat.Prime 183167 := by norm_num

private theorem prime_oneHundredTwentySevenDU_186581 : Nat.Prime 186581 := by norm_num

private theorem prime_oneHundredTwentySevenDU_189653 : Nat.Prime 189653 := by norm_num

private theorem prime_oneHundredTwentySevenDU_212677 : Nat.Prime 212677 := by norm_num

private theorem prime_oneHundredTwentySevenDU_215261 : Nat.Prime 215261 := by norm_num

private theorem prime_oneHundredTwentySevenDU_217411 : Nat.Prime 217411 := by norm_num

private theorem prime_oneHundredTwentySevenDU_235877 : Nat.Prime 235877 := by norm_num

private theorem prime_oneHundredTwentySevenDU_245339 : Nat.Prime 245339 := by norm_num

private theorem prime_oneHundredTwentySevenDU_258101 : Nat.Prime 258101 := by norm_num

private theorem prime_oneHundredTwentySevenDU_267679 : Nat.Prime 267679 := by norm_num

private theorem prime_oneHundredTwentySevenDU_279767 : Nat.Prime 279767 := by norm_num

private theorem prime_oneHundredTwentySevenDU_297793 : Nat.Prime 297793 := by norm_num

private theorem prime_oneHundredTwentySevenDU_299681 : Nat.Prime 299681 := by norm_num

private theorem prime_oneHundredTwentySevenDU_300569 : Nat.Prime 300569 := by norm_num

private theorem prime_oneHundredTwentySevenDU_366941 : Nat.Prime 366941 := by norm_num

private theorem prime_oneHundredTwentySevenDU_373327 : Nat.Prime 373327 := by norm_num

private theorem prime_oneHundredTwentySevenDU_414691 : Nat.Prime 414691 := by norm_num

private theorem prime_oneHundredTwentySevenDU_419687 : Nat.Prime 419687 := by norm_num

private theorem prime_oneHundredTwentySevenDU_434293 : Nat.Prime 434293 := by norm_num

private theorem prime_oneHundredTwentySevenDU_450533 : Nat.Prime 450533 := by norm_num

private theorem prime_oneHundredTwentySevenDU_453227 : Nat.Prime 453227 := by norm_num

private theorem prime_oneHundredTwentySevenDU_512747 : Nat.Prime 512747 := by norm_num

private theorem prime_oneHundredTwentySevenDU_524231 : Nat.Prime 524231 := by norm_num

private theorem prime_oneHundredTwentySevenDU_549097 : Nat.Prime 549097 := by norm_num

private theorem prime_oneHundredTwentySevenDU_572329 : Nat.Prime 572329 := by norm_num

private theorem prime_oneHundredTwentySevenDU_589357 : Nat.Prime 589357 := by norm_num

private theorem prime_oneHundredTwentySevenDU_639563 : Nat.Prime 639563 := by norm_num

private theorem prime_oneHundredTwentySevenDU_672181 : Nat.Prime 672181 := by norm_num

private theorem prime_oneHundredTwentySevenDU_738421 : Nat.Prime 738421 := by norm_num

private theorem prime_oneHundredTwentySevenDU_766861 : Nat.Prime 766861 := by norm_num

private theorem prime_oneHundredTwentySevenDU_789739 : Nat.Prime 789739 := by norm_num

private theorem prime_oneHundredTwentySevenDU_790583 : Nat.Prime 790583 := by norm_num

private theorem prime_oneHundredTwentySevenDU_795251 : Nat.Prime 795251 := by norm_num

private theorem prime_oneHundredTwentySevenDU_802799 : Nat.Prime 802799 := by norm_num

private theorem prime_oneHundredTwentySevenDU_810457 : Nat.Prime 810457 := by norm_num

private theorem prime_oneHundredTwentySevenDU_859361 : Nat.Prime 859361 := by norm_num

private theorem prime_oneHundredTwentySevenDU_863887 : Nat.Prime 863887 := by norm_num

private theorem prime_oneHundredTwentySevenDU_869203 : Nat.Prime 869203 := by norm_num

private theorem prime_oneHundredTwentySevenDU_917923 : Nat.Prime 917923 := by norm_num

private theorem prime_oneHundredTwentySevenDU_924551 : Nat.Prime 924551 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1033841 : Nat.Prime 1033841 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1043401 : Nat.Prime 1043401 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1051591 : Nat.Prime 1051591 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1080523 : Nat.Prime 1080523 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1091939 : Nat.Prime 1091939 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1198343 : Nat.Prime 1198343 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1241651 : Nat.Prime 1241651 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1246207 : Nat.Prime 1246207 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1285061 : Nat.Prime 1285061 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1329397 : Nat.Prime 1329397 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1364303 : Nat.Prime 1364303 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1450489 : Nat.Prime 1450489 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1499167 : Nat.Prime 1499167 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1506997 : Nat.Prime 1506997 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1507091 : Nat.Prime 1507091 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1521781 : Nat.Prime 1521781 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1541209 : Nat.Prime 1541209 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1664549 : Nat.Prime 1664549 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1772893 : Nat.Prime 1772893 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1783319 : Nat.Prime 1783319 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1790071 : Nat.Prime 1790071 := by norm_num

private theorem prime_oneHundredTwentySevenDU_1792121 : Nat.Prime 1792121 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2012383 : Nat.Prime 2012383 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2013049 : Nat.Prime 2013049 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2061613 : Nat.Prime 2061613 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2154329 : Nat.Prime 2154329 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2196401 : Nat.Prime 2196401 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2243453 : Nat.Prime 2243453 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2358637 : Nat.Prime 2358637 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2405063 : Nat.Prime 2405063 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2455183 : Nat.Prime 2455183 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2581097 : Nat.Prime 2581097 := by norm_num

private theorem prime_oneHundredTwentySevenDU_2935057 : Nat.Prime 2935057 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3042023 : Nat.Prime 3042023 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3076933 : Nat.Prime 3076933 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3174337 : Nat.Prime 3174337 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3300179 : Nat.Prime 3300179 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3471901 : Nat.Prime 3471901 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3514499 : Nat.Prime 3514499 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3699331 : Nat.Prime 3699331 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3772627 : Nat.Prime 3772627 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3829219 : Nat.Prime 3829219 := by norm_num

private theorem prime_oneHundredTwentySevenDU_3915511 : Nat.Prime 3915511 := by norm_num

private theorem prime_oneHundredTwentySevenDU_4194863 : Nat.Prime 4194863 := by norm_num

private theorem prime_oneHundredTwentySevenDU_4253941 : Nat.Prime 4253941 := by norm_num

private theorem prime_oneHundredTwentySevenDU_4436687 : Nat.Prime 4436687 := by norm_num

private theorem prime_oneHundredTwentySevenDU_4570067 : Nat.Prime 4570067 := by norm_num

private theorem prime_oneHundredTwentySevenDU_5095117 : Nat.Prime 5095117 := by norm_num

private theorem prime_oneHundredTwentySevenDU_5284649 : Nat.Prime 5284649 := by norm_num

private theorem prime_oneHundredTwentySevenDU_5378719 : Nat.Prime 5378719 := by norm_num

private theorem prime_oneHundredTwentySevenDU_5711411 : Nat.Prime 5711411 := by norm_num

private theorem prime_oneHundredTwentySevenDU_5916769 : Nat.Prime 5916769 := by norm_num

private theorem prime_oneHundredTwentySevenDU_6500941 : Nat.Prime 6500941 := by norm_num

private theorem prime_oneHundredTwentySevenDU_7021997 : Nat.Prime 7021997 := by norm_num

private theorem prime_oneHundredTwentySevenDU_7189423 : Nat.Prime 7189423 := by norm_num

private theorem prime_oneHundredTwentySevenDU_7211429 : Nat.Prime 7211429 := by norm_num

private theorem prime_oneHundredTwentySevenDU_7838651 : Nat.Prime 7838651 := by norm_num

private theorem prime_oneHundredTwentySevenDU_8039201 : Nat.Prime 8039201 := by norm_num

private theorem prime_oneHundredTwentySevenDU_8210887 : Nat.Prime 8210887 := by norm_num

private theorem prime_oneHundredTwentySevenDU_8402917 : Nat.Prime 8402917 := by norm_num

private theorem prime_oneHundredTwentySevenDU_8498551 : Nat.Prime 8498551 := by norm_num

private theorem prime_oneHundredTwentySevenDU_8711489 : Nat.Prime 8711489 := by norm_num

private theorem prime_oneHundredTwentySevenDU_9166609 : Nat.Prime 9166609 := by norm_num

private theorem prime_oneHundredTwentySevenDU_9609673 : Nat.Prime 9609673 := by norm_num

private theorem prime_oneHundredTwentySevenDU_10064617 : Nat.Prime 10064617 := by norm_num

private theorem prime_oneHundredTwentySevenDU_10267633 : Nat.Prime 10267633 := by norm_num

private theorem prime_oneHundredTwentySevenDU_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTwentySevenDU_11179951 : Nat.Prime 11179951 := by norm_num

private theorem prime_oneHundredTwentySevenDU_11275463 : Nat.Prime 11275463 := by norm_num

private theorem prime_oneHundredTwentySevenDU_11292781 : Nat.Prime 11292781 := by norm_num

private theorem prime_oneHundredTwentySevenDU_12005219 : Nat.Prime 12005219 := by norm_num

private theorem prime_oneHundredTwentySevenDU_13676753 : Nat.Prime 13676753 := by norm_num

private theorem prime_oneHundredTwentySevenDU_14601493 : Nat.Prime 14601493 := by norm_num

private theorem prime_oneHundredTwentySevenDU_15252667 : Nat.Prime 15252667 := by norm_num

private theorem prime_oneHundredTwentySevenDU_16481981 : Nat.Prime 16481981 := by norm_num

private theorem prime_oneHundredTwentySevenDU_17376563 : Nat.Prime 17376563 := by norm_num

private theorem prime_oneHundredTwentySevenDU_19093051 : Nat.Prime 19093051 := by norm_num

private theorem prime_oneHundredTwentySevenDU_20145847 : Nat.Prime 20145847 := by norm_num

private theorem prime_oneHundredTwentySevenDU_20853541 : Nat.Prime 20853541 := by norm_num

private theorem prime_oneHundredTwentySevenDU_20915299 : Nat.Prime 20915299 := by norm_num

private theorem prime_oneHundredTwentySevenDU_21092611 : Nat.Prime 21092611 := by norm_num

private theorem prime_oneHundredTwentySevenDU_21114209 : Nat.Prime 21114209 := by norm_num

private theorem prime_oneHundredTwentySevenDU_23463317 : Nat.Prime 23463317 := by norm_num

private theorem prime_oneHundredTwentySevenDU_23998231 : Nat.Prime 23998231 := by norm_num

private theorem prime_oneHundredTwentySevenDU_24052801 : Nat.Prime 24052801 := by norm_num

private theorem prime_oneHundredTwentySevenDU_25688083 : Nat.Prime 25688083 := by norm_num

private theorem prime_oneHundredTwentySevenDU_25835167 : Nat.Prime 25835167 := by norm_num

private theorem prime_oneHundredTwentySevenDU_26842349 : Nat.Prime 26842349 := by norm_num

private theorem prime_oneHundredTwentySevenDU_29936551 : Nat.Prime 29936551 := by norm_num

private theorem prime_oneHundredTwentySevenDU_30744827 : Nat.Prime 30744827 := by
  apply lucas_primality 30744827 (2 : ZMod 30744827)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (67, 1), (73, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (67, 1), (73, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 30744827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_67
      · exact prime_oneHundredTwentySevenDU_73
      · exact prime_oneHundredTwentySevenDU_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30744827) ^ 15372413 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30744827) ^ 4392118 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30744827) ^ 458878 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30744827) ^ 421162 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 30744827) ^ 68474 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_30881281 : Nat.Prime 30881281 := by
  apply lucas_primality 30881281 (11 : ZMod 30881281)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (5, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (5, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) = 30881281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_4021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 30881281) ^ 15440640 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 30881281) ^ 10293760 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 30881281) ^ 6176256 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 30881281) ^ 7680 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_31706933 : Nat.Prime 31706933 := by
  apply lucas_primality 31706933 (2 : ZMod 31706933)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (149561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (149561, 1)] : List FactorBlock).map factorBlockValue).prod) = 31706933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_53
      · exact prime_oneHundredTwentySevenDU_149561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31706933) ^ 15853466 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 31706933) ^ 598244 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 31706933) ^ 212 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_31726141 : Nat.Prime 31726141 := by
  apply lucas_primality 31726141 (6 : ZMod 31726141)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (617, 1), (857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (617, 1), (857, 1)] : List FactorBlock).map factorBlockValue).prod) = 31726141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_617
      · exact prime_oneHundredTwentySevenDU_857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 31726141) ^ 15863070 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 31726141) ^ 10575380 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 31726141) ^ 6345228 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 31726141) ^ 51420 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 31726141) ^ 37020 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_34434971 : Nat.Prime 34434971 := by
  apply lucas_primality 34434971 (2 : ZMod 34434971)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (619, 1), (5563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (619, 1), (5563, 1)] : List FactorBlock).map factorBlockValue).prod) = 34434971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_619
      · exact prime_oneHundredTwentySevenDU_5563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34434971) ^ 17217485 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 34434971) ^ 6886994 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 34434971) ^ 55630 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 34434971) ^ 6190 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_34893797 : Nat.Prime 34893797 := by
  apply lucas_primality 34893797 (2 : ZMod 34893797)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1246207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1246207, 1)] : List FactorBlock).map factorBlockValue).prod) = 34893797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_1246207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34893797) ^ 17446898 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 34893797) ^ 4984828 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 34893797) ^ 28 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_35842421 : Nat.Prime 35842421 := by
  apply lucas_primality 35842421 (7 : ZMod 35842421)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1792121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1792121, 1)] : List FactorBlock).map factorBlockValue).prod) = 35842421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_1792121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 35842421) ^ 17921210 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 35842421) ^ 7168484 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 35842421) ^ 20 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_36613249 : Nat.Prime 36613249 := by
  apply lucas_primality 36613249 (19 : ZMod 36613249)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (7, 1), (53, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (7, 1), (53, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 36613249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_53
      · exact prime_oneHundredTwentySevenDU_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 36613249) ^ 18306624 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (19 : ZMod 36613249) ^ 12204416 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (19 : ZMod 36613249) ^ 5230464 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (19 : ZMod 36613249) ^ 690816 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (19 : ZMod 36613249) ^ 142464 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_38438693 : Nat.Prime 38438693 := by
  apply lucas_primality 38438693 (2 : ZMod 38438693)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9609673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9609673, 1)] : List FactorBlock).map factorBlockValue).prod) = 38438693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_9609673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 38438693) ^ 19219346 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 38438693) ^ 4 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_43572937 : Nat.Prime 43572937 := by
  apply lucas_primality 43572937 (5 : ZMod 43572937)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (165049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (165049, 1)] : List FactorBlock).map factorBlockValue).prod) = 43572937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_165049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 43572937) ^ 21786468 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 43572937) ^ 14524312 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 43572937) ^ 3961176 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 43572937) ^ 264 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_43774729 : Nat.Prime 43774729 := by
  apply lucas_primality 43774729 (7 : ZMod 43774729)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (31, 1), (3461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (31, 1), (3461, 1)] : List FactorBlock).map factorBlockValue).prod) = 43774729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_31
      · exact prime_oneHundredTwentySevenDU_3461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 43774729) ^ 21887364 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 43774729) ^ 14591576 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 43774729) ^ 2574984 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 43774729) ^ 1412088 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 43774729) ^ 12648 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_45954367 : Nat.Prime 45954367 := by
  apply lucas_primality 45954367 (3 : ZMod 45954367)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (450533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (450533, 1)] : List FactorBlock).map factorBlockValue).prod) = 45954367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_450533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45954367) ^ 22977183 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 45954367) ^ 15318122 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 45954367) ^ 2703198 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 45954367) ^ 102 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_48627421 : Nat.Prime 48627421 := by
  apply lucas_primality 48627421 (2 : ZMod 48627421)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (810457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (810457, 1)] : List FactorBlock).map factorBlockValue).prod) = 48627421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_810457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48627421) ^ 24313710 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 48627421) ^ 16209140 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 48627421) ^ 9725484 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 48627421) ^ 60 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_50951171 : Nat.Prime 50951171 := by
  apply lucas_primality 50951171 (2 : ZMod 50951171)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5095117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5095117, 1)] : List FactorBlock).map factorBlockValue).prod) = 50951171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_5095117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50951171) ^ 25475585 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 50951171) ^ 10190234 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 50951171) ^ 10 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_52318543 : Nat.Prime 52318543 := by
  apply lucas_primality 52318543 (3 : ZMod 52318543)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (212677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (212677, 1)] : List FactorBlock).map factorBlockValue).prod) = 52318543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_41
      · exact prime_oneHundredTwentySevenDU_212677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 52318543) ^ 26159271 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 52318543) ^ 17439514 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 52318543) ^ 1276062 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 52318543) ^ 246 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_52530437 : Nat.Prime 52530437 := by
  apply lucas_primality 52530437 (2 : ZMod 52530437)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (81569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (81569, 1)] : List FactorBlock).map factorBlockValue).prod) = 52530437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_23
      · exact prime_oneHundredTwentySevenDU_81569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52530437) ^ 26265218 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 52530437) ^ 7504348 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 52530437) ^ 2283932 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 52530437) ^ 644 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_53026319 : Nat.Prime 53026319 := by
  apply lucas_primality 53026319 (11 : ZMod 53026319)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (947, 1), (27997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (947, 1), (27997, 1)] : List FactorBlock).map factorBlockValue).prod) = 53026319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_947
      · exact prime_oneHundredTwentySevenDU_27997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 53026319) ^ 26513159 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 53026319) ^ 55994 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 53026319) ^ 1894 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_54103169 : Nat.Prime 54103169 := by
  apply lucas_primality 54103169 (6 : ZMod 54103169)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (60383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (60383, 1)] : List FactorBlock).map factorBlockValue).prod) = 54103169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_60383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 54103169) ^ 27051584 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 54103169) ^ 7729024 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 54103169) ^ 896 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_55075381 : Nat.Prime 55075381 := by
  apply lucas_primality 55075381 (2 : ZMod 55075381)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (917923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (917923, 1)] : List FactorBlock).map factorBlockValue).prod) = 55075381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_917923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55075381) ^ 27537690 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 55075381) ^ 18358460 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 55075381) ^ 11015076 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 55075381) ^ 60 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_55685173 : Nat.Prime 55685173 := by
  apply lucas_primality 55685173 (2 : ZMod 55685173)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (311, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (311, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) = 55685173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_311
      · exact prime_oneHundredTwentySevenDU_347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55685173) ^ 27842586 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 55685173) ^ 18561724 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 55685173) ^ 1295004 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 55685173) ^ 179052 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 55685173) ^ 160476 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_57069427 : Nat.Prime 57069427 := by
  apply lucas_primality 57069427 (2 : ZMod 57069427)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (269, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (269, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) = 57069427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_269
      · exact prime_oneHundredTwentySevenDU_1861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57069427) ^ 28534713 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57069427) ^ 19023142 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57069427) ^ 3003654 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57069427) ^ 212154 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 57069427) ^ 30666 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_66919751 : Nat.Prime 66919751 := by
  apply lucas_primality 66919751 (13 : ZMod 66919751)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (267679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (267679, 1)] : List FactorBlock).map factorBlockValue).prod) = 66919751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_267679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 66919751) ^ 33459875 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 66919751) ^ 13383950 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 66919751) ^ 250 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_67201723 : Nat.Prime 67201723 := by
  apply lucas_primality 67201723 (2 : ZMod 67201723)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23, 1), (23189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23, 1), (23189, 1)] : List FactorBlock).map factorBlockValue).prod) = 67201723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_23
      · exact prime_oneHundredTwentySevenDU_23189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67201723) ^ 33600861 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 67201723) ^ 22400574 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 67201723) ^ 9600246 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 67201723) ^ 2921814 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 67201723) ^ 2898 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_67652779 : Nat.Prime 67652779 := by
  apply lucas_primality 67652779 (3 : ZMod 67652779)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11275463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11275463, 1)] : List FactorBlock).map factorBlockValue).prod) = 67652779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11275463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 67652779) ^ 33826389 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 67652779) ^ 22550926 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 67652779) ^ 6 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_76570939 : Nat.Prime 76570939 := by
  apply lucas_primality 76570939 (2 : ZMod 76570939)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4253941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4253941, 1)] : List FactorBlock).map factorBlockValue).prod) = 76570939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_4253941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 76570939) ^ 38285469 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 76570939) ^ 25523646 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 76570939) ^ 18 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_82374727 : Nat.Prime 82374727 := by
  apply lucas_primality 82374727 (5 : ZMod 82374727)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (179, 1), (10957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (179, 1), (10957, 1)] : List FactorBlock).map factorBlockValue).prod) = 82374727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_179
      · exact prime_oneHundredTwentySevenDU_10957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 82374727) ^ 41187363 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 82374727) ^ 27458242 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 82374727) ^ 11767818 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 82374727) ^ 460194 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 82374727) ^ 7518 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_82598627 : Nat.Prime 82598627 := by
  apply lucas_primality 82598627 (2 : ZMod 82598627)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (181, 1), (20743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (181, 1), (20743, 1)] : List FactorBlock).map factorBlockValue).prod) = 82598627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_181
      · exact prime_oneHundredTwentySevenDU_20743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82598627) ^ 41299313 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 82598627) ^ 7508966 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 82598627) ^ 456346 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 82598627) ^ 3982 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_88386589 : Nat.Prime 88386589 := by
  apply lucas_primality 88386589 (6 : ZMod 88386589)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2455183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2455183, 1)] : List FactorBlock).map factorBlockValue).prod) = 88386589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_2455183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 88386589) ^ 44193294 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 88386589) ^ 29462196 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 88386589) ^ 36 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_102752333 : Nat.Prime 102752333 := by
  apply lucas_primality 102752333 (2 : ZMod 102752333)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (25688083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (25688083, 1)] : List FactorBlock).map factorBlockValue).prod) = 102752333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_25688083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 102752333) ^ 51376166 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 102752333) ^ 4 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_103057499 : Nat.Prime 103057499 := by
  apply lucas_primality 103057499 (2 : ZMod 103057499)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (1198343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (1198343, 1)] : List FactorBlock).map factorBlockValue).prod) = 103057499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_1198343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103057499) ^ 51528749 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103057499) ^ 2396686 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103057499) ^ 86 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_107927459 : Nat.Prime 107927459 := by
  apply lucas_primality 107927459 (2 : ZMod 107927459)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (3174337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (3174337, 1)] : List FactorBlock).map factorBlockValue).prod) = 107927459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_3174337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 107927459) ^ 53963729 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 107927459) ^ 6348674 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 107927459) ^ 34 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_114878371 : Nat.Prime 114878371 := by
  apply lucas_primality 114878371 (10 : ZMod 114878371)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (43, 2), (109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (43, 2), (109, 1)] : List FactorBlock).map factorBlockValue).prod) = 114878371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 114878371) ^ 57439185 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 114878371) ^ 38292790 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 114878371) ^ 22975674 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 114878371) ^ 6046230 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 114878371) ^ 2671590 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 114878371) ^ 1053930 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_125562551 : Nat.Prime 125562551 := by
  apply lucas_primality 125562551 (7 : ZMod 125562551)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (109, 1), (23039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (109, 1), (23039, 1)] : List FactorBlock).map factorBlockValue).prod) = 125562551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_109
      · exact prime_oneHundredTwentySevenDU_23039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 125562551) ^ 62781275 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 125562551) ^ 25112510 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 125562551) ^ 1151950 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 125562551) ^ 5450 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_131981867 : Nat.Prime 131981867 := by
  apply lucas_primality 131981867 (2 : ZMod 131981867)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (23, 1), (151009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (23, 1), (151009, 1)] : List FactorBlock).map factorBlockValue).prod) = 131981867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_23
      · exact prime_oneHundredTwentySevenDU_151009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 131981867) ^ 65990933 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131981867) ^ 6946414 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131981867) ^ 5738342 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131981867) ^ 874 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_146308961 : Nat.Prime 146308961 := by
  apply lucas_primality 146308961 (15 : ZMod 146308961)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (130633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (130633, 1)] : List FactorBlock).map factorBlockValue).prod) = 146308961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_130633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 146308961) ^ 73154480 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (15 : ZMod 146308961) ^ 29261792 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (15 : ZMod 146308961) ^ 20901280 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (15 : ZMod 146308961) ^ 1120 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_158059799 : Nat.Prime 158059799 := by
  apply lucas_primality 158059799 (7 : ZMod 158059799)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (197, 1), (30859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (197, 1), (30859, 1)] : List FactorBlock).map factorBlockValue).prod) = 158059799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_197
      · exact prime_oneHundredTwentySevenDU_30859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 158059799) ^ 79029899 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 158059799) ^ 12158446 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 158059799) ^ 802334 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 158059799) ^ 5122 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_166564751 : Nat.Prime 166564751 := by
  apply lucas_primality 166564751 (13 : ZMod 166564751)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (11, 1), (37, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (11, 1), (37, 1), (1637, 1)] : List FactorBlock).map factorBlockValue).prod) = 166564751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_37
      · exact prime_oneHundredTwentySevenDU_1637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 166564751) ^ 83282375 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 166564751) ^ 33312950 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 166564751) ^ 15142250 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 166564751) ^ 4501750 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 166564751) ^ 101750 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_174706253 : Nat.Prime 174706253 := by
  apply lucas_primality 174706253 (2 : ZMod 174706253)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (67, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (67, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 174706253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_23
      · exact prime_oneHundredTwentySevenDU_67
      · exact prime_oneHundredTwentySevenDU_4049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 174706253) ^ 87353126 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 174706253) ^ 24958036 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 174706253) ^ 7595924 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 174706253) ^ 2607556 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 174706253) ^ 43148 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_180211393 : Nat.Prime 180211393 := by
  apply lucas_primality 180211393 (7 : ZMod 180211393)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (34763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (34763, 1)] : List FactorBlock).map factorBlockValue).prod) = 180211393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_34763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 180211393) ^ 90105696 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 180211393) ^ 60070464 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 180211393) ^ 5184 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_190149683 : Nat.Prime 190149683 := by
  apply lucas_primality 190149683 (2 : ZMod 190149683)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (79, 1), (97, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (79, 1), (97, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) = 190149683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_79
      · exact prime_oneHundredTwentySevenDU_97
      · exact prime_oneHundredTwentySevenDU_653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 190149683) ^ 95074841 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 190149683) ^ 10007878 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 190149683) ^ 2406958 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 190149683) ^ 1960306 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 190149683) ^ 291194 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_191085757 : Nat.Prime 191085757 := by
  apply lucas_primality 191085757 (2 : ZMod 191085757)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (549097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (549097, 1)] : List FactorBlock).map factorBlockValue).prod) = 191085757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_29
      · exact prime_oneHundredTwentySevenDU_549097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 191085757) ^ 95542878 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 191085757) ^ 63695252 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 191085757) ^ 6589164 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 191085757) ^ 348 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_208314061 : Nat.Prime 208314061 := by
  apply lucas_primality 208314061 (6 : ZMod 208314061)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (3471901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (3471901, 1)] : List FactorBlock).map factorBlockValue).prod) = 208314061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_3471901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 208314061) ^ 104157030 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 208314061) ^ 69438020 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 208314061) ^ 41662812 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 208314061) ^ 60 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_225625123 : Nat.Prime 225625123 := by
  apply lucas_primality 225625123 (5 : ZMod 225625123)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (107, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (107, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) = 225625123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_107
      · exact prime_oneHundredTwentySevenDU_2297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 225625123) ^ 112812561 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 225625123) ^ 75208374 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 225625123) ^ 13272066 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 225625123) ^ 2108646 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 225625123) ^ 98226 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_258351671 : Nat.Prime 258351671 := by
  apply lucas_primality 258351671 (7 : ZMod 258351671)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (25835167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (25835167, 1)] : List FactorBlock).map factorBlockValue).prod) = 258351671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_25835167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 258351671) ^ 129175835 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 258351671) ^ 51670334 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 258351671) ^ 10 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_265634557 : Nat.Prime 265634557 := by
  apply lucas_primality 265634557 (2 : ZMod 265634557)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (2012383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (2012383, 1)] : List FactorBlock).map factorBlockValue).prod) = 265634557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_2012383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 265634557) ^ 132817278 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 265634557) ^ 88544852 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 265634557) ^ 24148596 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 265634557) ^ 132 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_287576921 : Nat.Prime 287576921 := by
  apply lucas_primality 287576921 (3 : ZMod 287576921)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7189423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7189423, 1)] : List FactorBlock).map factorBlockValue).prod) = 287576921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_7189423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 287576921) ^ 143788460 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 287576921) ^ 57515384 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 287576921) ^ 40 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_287978773 : Nat.Prime 287978773 := by
  apply lucas_primality 287978773 (2 : ZMod 287978773)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23998231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23998231, 1)] : List FactorBlock).map factorBlockValue).prod) = 287978773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_23998231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 287978773) ^ 143989386 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 287978773) ^ 95992924 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 287978773) ^ 12 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_308631047 : Nat.Prime 308631047 := by
  apply lucas_primality 308631047 (5 : ZMod 308631047)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (163, 1), (20143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (163, 1), (20143, 1)] : List FactorBlock).map factorBlockValue).prod) = 308631047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_47
      · exact prime_oneHundredTwentySevenDU_163
      · exact prime_oneHundredTwentySevenDU_20143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 308631047) ^ 154315523 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 308631047) ^ 6566618 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 308631047) ^ 1893442 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 308631047) ^ 15322 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_320175899 : Nat.Prime 320175899 := by
  apply lucas_primality 320175899 (2 : ZMod 320175899)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (89, 1), (36709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (89, 1), (36709, 1)] : List FactorBlock).map factorBlockValue).prod) = 320175899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_89
      · exact prime_oneHundredTwentySevenDU_36709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 320175899) ^ 160087949 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 320175899) ^ 45739414 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 320175899) ^ 3597482 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 320175899) ^ 8722 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_323626187 : Nat.Prime 323626187 := by
  apply lucas_primality 323626187 (2 : ZMod 323626187)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (79, 1), (157559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (79, 1), (157559, 1)] : List FactorBlock).map factorBlockValue).prod) = 323626187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_79
      · exact prime_oneHundredTwentySevenDU_157559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 323626187) ^ 161813093 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 323626187) ^ 24894322 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 323626187) ^ 4096534 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 323626187) ^ 2054 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_335885119 : Nat.Prime 335885119 := by
  apply lucas_primality 335885119 (3 : ZMod 335885119)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (766861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (766861, 1)] : List FactorBlock).map factorBlockValue).prod) = 335885119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_73
      · exact prime_oneHundredTwentySevenDU_766861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 335885119) ^ 167942559 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 335885119) ^ 111961706 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 335885119) ^ 4601166 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 335885119) ^ 438 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_372185651 : Nat.Prime 372185651 := by
  apply lucas_primality 372185651 (2 : ZMod 372185651)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1423, 1), (5231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1423, 1), (5231, 1)] : List FactorBlock).map factorBlockValue).prod) = 372185651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_1423
      · exact prime_oneHundredTwentySevenDU_5231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 372185651) ^ 186092825 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 372185651) ^ 74437130 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 372185651) ^ 261550 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 372185651) ^ 71150 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_393138017 : Nat.Prime 393138017 := by
  apply lucas_primality 393138017 (3 : ZMod 393138017)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (313, 1), (39251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (313, 1), (39251, 1)] : List FactorBlock).map factorBlockValue).prod) = 393138017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_313
      · exact prime_oneHundredTwentySevenDU_39251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 393138017) ^ 196569008 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 393138017) ^ 1256032 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 393138017) ^ 10016 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_446677393 : Nat.Prime 446677393 := by
  apply lucas_primality 446677393 (10 : ZMod 446677393)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (1329397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (1329397, 1)] : List FactorBlock).map factorBlockValue).prod) = 446677393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_1329397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 446677393) ^ 223338696 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 446677393) ^ 148892464 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 446677393) ^ 63811056 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 446677393) ^ 336 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_534167129 : Nat.Prime 534167129 := by
  apply lucas_primality 534167129 (3 : ZMod 534167129)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (293, 1), (20717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (293, 1), (20717, 1)] : List FactorBlock).map factorBlockValue).prod) = 534167129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_293
      · exact prime_oneHundredTwentySevenDU_20717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 534167129) ^ 267083564 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 534167129) ^ 48560648 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 534167129) ^ 1823096 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 534167129) ^ 25784 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_544522697 : Nat.Prime 544522697 := by
  apply lucas_primality 544522697 (3 : ZMod 544522697)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3109, 1), (21893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3109, 1), (21893, 1)] : List FactorBlock).map factorBlockValue).prod) = 544522697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3109
      · exact prime_oneHundredTwentySevenDU_21893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 544522697) ^ 272261348 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 544522697) ^ 175144 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 544522697) ^ 24872 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_555373381 : Nat.Prime 555373381 := by
  apply lucas_primality 555373381 (7 : ZMod 555373381)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (43, 1), (215261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (43, 1), (215261, 1)] : List FactorBlock).map factorBlockValue).prod) = 555373381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_215261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 555373381) ^ 277686690 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 555373381) ^ 185124460 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 555373381) ^ 111074676 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 555373381) ^ 12915660 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 555373381) ^ 2580 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_566321023 : Nat.Prime 566321023 := by
  apply lucas_primality 566321023 (3 : ZMod 566321023)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (197, 1), (159707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (197, 1), (159707, 1)] : List FactorBlock).map factorBlockValue).prod) = 566321023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_197
      · exact prime_oneHundredTwentySevenDU_159707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 566321023) ^ 283160511 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 566321023) ^ 188773674 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 566321023) ^ 2874726 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 566321023) ^ 3546 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_567628811 : Nat.Prime 567628811 := by
  apply lucas_primality 567628811 (2 : ZMod 567628811)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (43, 1), (11093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (43, 1), (11093, 1)] : List FactorBlock).map factorBlockValue).prod) = 567628811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_11093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 567628811) ^ 283814405 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 567628811) ^ 113525762 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 567628811) ^ 81089830 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 567628811) ^ 33389930 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 567628811) ^ 13200670 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 567628811) ^ 51170 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_595873081 : Nat.Prime 595873081 := by
  apply lucas_primality 595873081 (7 : ZMod 595873081)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (11, 1), (150473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (11, 1), (150473, 1)] : List FactorBlock).map factorBlockValue).prod) = 595873081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_150473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 595873081) ^ 297936540 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 595873081) ^ 198624360 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 595873081) ^ 119174616 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 595873081) ^ 54170280 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 595873081) ^ 3960 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_626305439 : Nat.Prime 626305439 := by
  apply lucas_primality 626305439 (11 : ZMod 626305439)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (37, 1), (113, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (37, 1), (113, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) = 626305439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_37
      · exact prime_oneHundredTwentySevenDU_113
      · exact prime_oneHundredTwentySevenDU_619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 626305439) ^ 313152719 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 626305439) ^ 56936858 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 626305439) ^ 16927174 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 626305439) ^ 5542526 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 626305439) ^ 1011802 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_17203
      · exact prime_oneHundredTwentySevenDU_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_734797933 : Nat.Prime 734797933 := by
  apply lucas_primality 734797933 (5 : ZMod 734797933)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (43, 1), (129457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (43, 1), (129457, 1)] : List FactorBlock).map factorBlockValue).prod) = 734797933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_129457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 734797933) ^ 367398966 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 734797933) ^ 244932644 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 734797933) ^ 66799812 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 734797933) ^ 17088324 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 734797933) ^ 5676 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_810863813 : Nat.Prime 810863813 := by
  apply lucas_primality 810863813 (2 : ZMod 810863813)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (727, 1), (25349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (727, 1), (25349, 1)] : List FactorBlock).map factorBlockValue).prod) = 810863813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_727
      · exact prime_oneHundredTwentySevenDU_25349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 810863813) ^ 405431906 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 810863813) ^ 73714892 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 810863813) ^ 1115356 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 810863813) ^ 31988 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_861551419 : Nat.Prime 861551419 := by
  apply lucas_primality 861551419 (3 : ZMod 861551419)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (13, 1), (173, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (13, 1), (173, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) = 861551419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_173
      · exact prime_oneHundredTwentySevenDU_1303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 861551419) ^ 430775709 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 861551419) ^ 287183806 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 861551419) ^ 123078774 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 861551419) ^ 66273186 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 861551419) ^ 4980066 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 861551419) ^ 661206 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_878760479 : Nat.Prime 878760479 := by
  apply lucas_primality 878760479 (7 : ZMod 878760479)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (1031, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (1031, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) = 878760479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_229
      · exact prime_oneHundredTwentySevenDU_1031
      · exact prime_oneHundredTwentySevenDU_1861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 878760479) ^ 439380239 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 878760479) ^ 3837382 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 878760479) ^ 852338 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 878760479) ^ 472198 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_925964387 : Nat.Prime 925964387 := by
  apply lucas_primality 925964387 (2 : ZMod 925964387)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9941, 1), (46573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9941, 1), (46573, 1)] : List FactorBlock).map factorBlockValue).prod) = 925964387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_9941
      · exact prime_oneHundredTwentySevenDU_46573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 925964387) ^ 462982193 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 925964387) ^ 93146 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 925964387) ^ 19882 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1013188073 : Nat.Prime 1013188073 := by
  apply lucas_primality 1013188073 (3 : ZMod 1013188073)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (19, 1), (512747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (19, 1), (512747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1013188073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_512747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1013188073) ^ 506594036 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013188073) ^ 77937544 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013188073) ^ 53325688 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1013188073) ^ 1976 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1115711969 : Nat.Prime 1115711969 := by
  apply lucas_primality 1115711969 (3 : ZMod 1115711969)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (23, 1), (30937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (23, 1), (30937, 1)] : List FactorBlock).map factorBlockValue).prod) = 1115711969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_23
      · exact prime_oneHundredTwentySevenDU_30937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1115711969) ^ 557855984 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115711969) ^ 159387424 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115711969) ^ 48509216 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1115711969) ^ 36064 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1135257623 : Nat.Prime 1135257623 := by
  apply lucas_primality 1135257623 (5 : ZMod 1135257623)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (567628811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (567628811, 1)] : List FactorBlock).map factorBlockValue).prod) = 1135257623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_567628811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1135257623) ^ 567628811 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1135257623) ^ 2 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1148783711 : Nat.Prime 1148783711 := by
  apply lucas_primality 1148783711 (11 : ZMod 1148783711)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (114878371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (114878371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1148783711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_114878371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1148783711) ^ 574391855 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1148783711) ^ 229756742 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1148783711) ^ 10 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1186968193 : Nat.Prime 1186968193 := by
  apply lucas_primality 1186968193 (5 : ZMod 1186968193)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (1193, 1), (2591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (1193, 1), (2591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1186968193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_1193
      · exact prime_oneHundredTwentySevenDU_2591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1186968193) ^ 593484096 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1186968193) ^ 395656064 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1186968193) ^ 994944 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1186968193) ^ 458112 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1205044559 : Nat.Prime 1205044559 := by
  apply lucas_primality 1205044559 (11 : ZMod 1205044559)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (331, 1), (107077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (331, 1), (107077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205044559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_331
      · exact prime_oneHundredTwentySevenDU_107077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1205044559) ^ 602522279 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1205044559) ^ 70884974 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1205044559) ^ 3640618 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1205044559) ^ 11254 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1238039419 : Nat.Prime 1238039419 := by
  apply lucas_primality 1238039419 (3 : ZMod 1238039419)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (257, 1), (10427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (257, 1), (10427, 1)] : List FactorBlock).map factorBlockValue).prod) = 1238039419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_257
      · exact prime_oneHundredTwentySevenDU_10427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1238039419) ^ 619019709 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238039419) ^ 412679806 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238039419) ^ 176862774 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238039419) ^ 112549038 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238039419) ^ 4817274 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238039419) ^ 118734 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1291981321 : Nat.Prime 1291981321 := by
  apply lucas_primality 1291981321 (13 : ZMod 1291981321)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 1), (29, 1), (71, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 1), (29, 1), (71, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291981321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_29
      · exact prime_oneHundredTwentySevenDU_71
      · exact prime_oneHundredTwentySevenDU_83
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1291981321) ^ 645990660 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 1291981321) ^ 430660440 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 1291981321) ^ 258396264 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 1291981321) ^ 184568760 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 1291981321) ^ 44551080 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 1291981321) ^ 18196920 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 1291981321) ^ 15566040 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1446533513 : Nat.Prime 1446533513 := by
  apply lucas_primality 1446533513 (3 : ZMod 1446533513)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (269, 1), (672181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (269, 1), (672181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1446533513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_269
      · exact prime_oneHundredTwentySevenDU_672181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1446533513) ^ 723266756 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1446533513) ^ 5377448 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1446533513) ^ 2152 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1482745087 : Nat.Prime 1482745087 := by
  apply lucas_primality 1482745087 (3 : ZMod 1482745087)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (82374727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (82374727, 1)] : List FactorBlock).map factorBlockValue).prod) = 1482745087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_82374727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1482745087) ^ 741372543 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1482745087) ^ 494248362 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1482745087) ^ 18 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1944504959 : Nat.Prime 1944504959 := by
  apply lucas_primality 1944504959 (11 : ZMod 1944504959)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (88386589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (88386589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1944504959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_88386589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1944504959) ^ 972252479 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1944504959) ^ 176773178 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 1944504959) ^ 22 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_2371526057 : Nat.Prime 2371526057 := by
  apply lucas_primality 2371526057 (3 : ZMod 2371526057)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (101, 1), (2935057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (101, 1), (2935057, 1)] : List FactorBlock).map factorBlockValue).prod) = 2371526057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_101
      · exact prime_oneHundredTwentySevenDU_2935057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2371526057) ^ 1185763028 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2371526057) ^ 23480456 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2371526057) ^ 808 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_2410089119 : Nat.Prime 2410089119 := by
  apply lucas_primality 2410089119 (7 : ZMod 2410089119)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1205044559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1205044559, 1)] : List FactorBlock).map factorBlockValue).prod) = 2410089119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_1205044559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 2410089119) ^ 1205044559 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2410089119) ^ 2 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_2496440873 : Nat.Prime 2496440873 := by
  apply lucas_primality 2496440873 (3 : ZMod 2496440873)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (1283, 1), (8387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (1283, 1), (8387, 1)] : List FactorBlock).map factorBlockValue).prod) = 2496440873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_29
      · exact prime_oneHundredTwentySevenDU_1283
      · exact prime_oneHundredTwentySevenDU_8387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2496440873) ^ 1248220436 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2496440873) ^ 86084168 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2496440873) ^ 1945784 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2496440873) ^ 297656 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_2599402321 : Nat.Prime 2599402321 := by
  apply lucas_primality 2599402321 (7 : ZMod 2599402321)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (337, 1), (3571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (337, 1), (3571, 1)] : List FactorBlock).map factorBlockValue).prod) = 2599402321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_337
      · exact prime_oneHundredTwentySevenDU_3571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2599402321) ^ 1299701160 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2599402321) ^ 866467440 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2599402321) ^ 519880464 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2599402321) ^ 7713360 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 2599402321) ^ 727920 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_2623875739 : Nat.Prime 2623875739 := by
  apply lucas_primality 2623875739 (2 : ZMod 2623875739)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (43, 1), (924551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (43, 1), (924551, 1)] : List FactorBlock).map factorBlockValue).prod) = 2623875739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_924551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2623875739) ^ 1311937869 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2623875739) ^ 874625246 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2623875739) ^ 238534158 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2623875739) ^ 61020366 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 2623875739) ^ 2838 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_3220956047 : Nat.Prime 3220956047 := by
  apply lucas_primality 3220956047 (10 : ZMod 3220956047)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (20915299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (20915299, 1)] : List FactorBlock).map factorBlockValue).prod) = 3220956047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_20915299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 3220956047) ^ 1610478023 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 3220956047) ^ 460136578 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 3220956047) ^ 292814186 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 3220956047) ^ 154 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_3335178349 : Nat.Prime 3335178349 := by
  apply lucas_primality 3335178349 (2 : ZMod 3335178349)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (30881281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (30881281, 1)] : List FactorBlock).map factorBlockValue).prod) = 3335178349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_30881281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3335178349) ^ 1667589174 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3335178349) ^ 1111726116 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3335178349) ^ 108 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_3358851191 : Nat.Prime 3358851191 := by
  apply lucas_primality 3358851191 (13 : ZMod 3358851191)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (335885119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (335885119, 1)] : List FactorBlock).map factorBlockValue).prod) = 3358851191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_335885119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3358851191) ^ 1679425595 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 3358851191) ^ 671770238 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 3358851191) ^ 10 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_3941837257 : Nat.Prime 3941837257 := by
  apply lucas_primality 3941837257 (5 : ZMod 3941837257)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (23463317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (23463317, 1)] : List FactorBlock).map factorBlockValue).prod) = 3941837257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_23463317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3941837257) ^ 1970918628 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3941837257) ^ 1313945752 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3941837257) ^ 563119608 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3941837257) ^ 168 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_4609985621 : Nat.Prime 4609985621 := by
  apply lucas_primality 4609985621 (2 : ZMod 4609985621)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3877, 1), (59453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3877, 1), (59453, 1)] : List FactorBlock).map factorBlockValue).prod) = 4609985621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_3877
      · exact prime_oneHundredTwentySevenDU_59453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4609985621) ^ 2304992810 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4609985621) ^ 921997124 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4609985621) ^ 1189060 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4609985621) ^ 77540 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_5066650103 : Nat.Prime 5066650103 := by
  apply lucas_primality 5066650103 (5 : ZMod 5066650103)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (181, 1), (297793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (181, 1), (297793, 1)] : List FactorBlock).map factorBlockValue).prod) = 5066650103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_47
      · exact prime_oneHundredTwentySevenDU_181
      · exact prime_oneHundredTwentySevenDU_297793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5066650103) ^ 2533325051 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5066650103) ^ 107801066 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5066650103) ^ 27992542 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 5066650103) ^ 17014 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_5388579181 : Nat.Prime 5388579181 := by
  apply lucas_primality 5388579181 (6 : ZMod 5388579181)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (29936551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (29936551, 1)] : List FactorBlock).map factorBlockValue).prod) = 5388579181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_29936551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5388579181) ^ 2694289590 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 5388579181) ^ 1796193060 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 5388579181) ^ 1077715836 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 5388579181) ^ 180 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_31
      · exact prime_oneHundredTwentySevenDU_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_6388991821 : Nat.Prime 6388991821 := by
  apply lucas_primality 6388991821 (17 : ZMod 6388991821)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (659, 1), (53861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (659, 1), (53861, 1)] : List FactorBlock).map factorBlockValue).prod) = 6388991821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_659
      · exact prime_oneHundredTwentySevenDU_53861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 6388991821) ^ 3194495910 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (17 : ZMod 6388991821) ^ 2129663940 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (17 : ZMod 6388991821) ^ 1277798364 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (17 : ZMod 6388991821) ^ 9694980 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (17 : ZMod 6388991821) ^ 118620 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_6439531807 : Nat.Prime 6439531807 := by
  apply lucas_primality 6439531807 (3 : ZMod 6439531807)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (151, 1), (789739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (151, 1), (789739, 1)] : List FactorBlock).map factorBlockValue).prod) = 6439531807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_151
      · exact prime_oneHundredTwentySevenDU_789739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6439531807) ^ 3219765903 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6439531807) ^ 2146510602 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6439531807) ^ 42645906 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6439531807) ^ 8154 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_7540610551 : Nat.Prime 7540610551 := by
  apply lucas_primality 7540610551 (15 : ZMod 7540610551)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (4570067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (4570067, 1)] : List FactorBlock).map factorBlockValue).prod) = 7540610551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_4570067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 7540610551) ^ 3770305275 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (15 : ZMod 7540610551) ^ 2513536850 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (15 : ZMod 7540610551) ^ 1508122110 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (15 : ZMod 7540610551) ^ 685510050 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (15 : ZMod 7540610551) ^ 1650 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_7869584039 : Nat.Prime 7869584039 := by
  apply lucas_primality 7869584039 (7 : ZMod 7869584039)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3169, 1), (1241651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3169, 1), (1241651, 1)] : List FactorBlock).map factorBlockValue).prod) = 7869584039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3169
      · exact prime_oneHundredTwentySevenDU_1241651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 7869584039) ^ 3934792019 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 7869584039) ^ 2483302 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 7869584039) ^ 6338 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_9581440733 : Nat.Prime 9581440733 := by
  apply lucas_primality 9581440733 (2 : ZMod 9581440733)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (82598627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (82598627, 1)] : List FactorBlock).map factorBlockValue).prod) = 9581440733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_29
      · exact prime_oneHundredTwentySevenDU_82598627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9581440733) ^ 4790720366 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9581440733) ^ 330394508 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9581440733) ^ 116 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_9592671239 : Nat.Prime 9592671239 := by
  apply lucas_primality 9592671239 (7 : ZMod 9592671239)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (36613249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (36613249, 1)] : List FactorBlock).map factorBlockValue).prod) = 9592671239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_131
      · exact prime_oneHundredTwentySevenDU_36613249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 9592671239) ^ 4796335619 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 9592671239) ^ 73226498 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 9592671239) ^ 262 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_9604687237 : Nat.Prime 9604687237 := by
  apply lucas_primality 9604687237 (2 : ZMod 9604687237)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (997, 1), (802799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (997, 1), (802799, 1)] : List FactorBlock).map factorBlockValue).prod) = 9604687237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_997
      · exact prime_oneHundredTwentySevenDU_802799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9604687237) ^ 4802343618 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9604687237) ^ 3201562412 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9604687237) ^ 9633588 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 9604687237) ^ 11964 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_9826902647 : Nat.Prime 9826902647 := by
  apply lucas_primality 9826902647 (5 : ZMod 9826902647)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (446677393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (446677393, 1)] : List FactorBlock).map factorBlockValue).prod) = 9826902647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_446677393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 9826902647) ^ 4913451323 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 9826902647) ^ 893354786 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 9826902647) ^ 22 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_10133300207 : Nat.Prime 10133300207 := by
  apply lucas_primality 10133300207 (5 : ZMod 10133300207)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5066650103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5066650103, 1)] : List FactorBlock).map factorBlockValue).prod) = 10133300207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5066650103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 10133300207) ^ 5066650103 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 10133300207) ^ 2 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_11684947213 : Nat.Prime 11684947213 := by
  apply lucas_primality 11684947213 (2 : ZMod 11684947213)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (19093051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (19093051, 1)] : List FactorBlock).map factorBlockValue).prod) = 11684947213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_19093051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11684947213) ^ 5842473606 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11684947213) ^ 3894982404 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11684947213) ^ 687349836 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11684947213) ^ 612 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_11884359667 : Nat.Prime 11884359667 := by
  apply lucas_primality 11884359667 (3 : ZMod 11884359667)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (163, 1), (639563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (163, 1), (639563, 1)] : List FactorBlock).map factorBlockValue).prod) = 11884359667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_163
      · exact prime_oneHundredTwentySevenDU_639563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11884359667) ^ 5942179833 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11884359667) ^ 3961453222 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11884359667) ^ 625492614 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11884359667) ^ 72910182 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 11884359667) ^ 18582 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_13301637757 : Nat.Prime 13301637757 := by
  apply lucas_primality 13301637757 (2 : ZMod 13301637757)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (29, 1), (89, 1), (39043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (29, 1), (89, 1), (39043, 1)] : List FactorBlock).map factorBlockValue).prod) = 13301637757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_29
      · exact prime_oneHundredTwentySevenDU_89
      · exact prime_oneHundredTwentySevenDU_39043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13301637757) ^ 6650818878 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13301637757) ^ 4433879252 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13301637757) ^ 1209239796 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13301637757) ^ 458677164 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13301637757) ^ 149456604 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 13301637757) ^ 340692 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_14557926679 : Nat.Prime 14557926679 := by
  apply lucas_primality 14557926679 (3 : ZMod 14557926679)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (7607, 1), (10289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (7607, 1), (10289, 1)] : List FactorBlock).map factorBlockValue).prod) = 14557926679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_31
      · exact prime_oneHundredTwentySevenDU_7607
      · exact prime_oneHundredTwentySevenDU_10289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14557926679) ^ 7278963339 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14557926679) ^ 4852642226 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14557926679) ^ 469610538 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14557926679) ^ 1913754 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 14557926679) ^ 1414902 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_14700885673 : Nat.Prime 14700885673 := by
  apply lucas_primality 14700885673 (5 : ZMod 14700885673)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (55685173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (55685173, 1)] : List FactorBlock).map factorBlockValue).prod) = 14700885673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_55685173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14700885673) ^ 7350442836 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 14700885673) ^ 4900295224 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 14700885673) ^ 1336444152 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 14700885673) ^ 264 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_18033938933 : Nat.Prime 18033938933 := by
  apply lucas_primality 18033938933 (2 : ZMod 18033938933)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (57069427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (57069427, 1)] : List FactorBlock).map factorBlockValue).prod) = 18033938933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_79
      · exact prime_oneHundredTwentySevenDU_57069427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18033938933) ^ 9016969466 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18033938933) ^ 228277708 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 18033938933) ^ 316 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_19162881467 : Nat.Prime 19162881467 := by
  apply lucas_primality 19162881467 (2 : ZMod 19162881467)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9581440733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9581440733, 1)] : List FactorBlock).map factorBlockValue).prod) = 19162881467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_9581440733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 19162881467) ^ 9581440733 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 19162881467) ^ 2 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_20228077459 : Nat.Prime 20228077459 := by
  apply lucas_primality 20228077459 (2 : ZMod 20228077459)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (43, 1), (8711489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (43, 1), (8711489, 1)] : List FactorBlock).map factorBlockValue).prod) = 20228077459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_8711489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20228077459) ^ 10114038729 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 20228077459) ^ 6742692486 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 20228077459) ^ 470420406 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 20228077459) ^ 2322 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_22284709543 : Nat.Prime 22284709543 := by
  apply lucas_primality 22284709543 (3 : ZMod 22284709543)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1238039419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1238039419, 1)] : List FactorBlock).map factorBlockValue).prod) = 22284709543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_1238039419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 22284709543) ^ 11142354771 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 22284709543) ^ 7428236514 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 22284709543) ^ 18 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_26618759149 : Nat.Prime 26618759149 := by
  apply lucas_primality 26618759149 (6 : ZMod 26618759149)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (54103169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (54103169, 1)] : List FactorBlock).map factorBlockValue).prod) = 26618759149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_41
      · exact prime_oneHundredTwentySevenDU_54103169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 26618759149) ^ 13309379574 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 26618759149) ^ 8872919716 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 26618759149) ^ 649238028 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 26618759149) ^ 492 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_26894775517 : Nat.Prime 26894775517 := by
  apply lucas_primality 26894775517 (5 : ZMod 26894775517)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (320175899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (320175899, 1)] : List FactorBlock).map factorBlockValue).prod) = 26894775517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_320175899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 26894775517) ^ 13447387758 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 26894775517) ^ 8964925172 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 26894775517) ^ 3842110788 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 26894775517) ^ 84 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_28699649617 : Nat.Prime 28699649617 := by
  apply lucas_primality 28699649617 (10 : ZMod 28699649617)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (43, 1), (79, 1), (16001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (43, 1), (79, 1), (16001, 1)] : List FactorBlock).map factorBlockValue).prod) = 28699649617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_79
      · exact prime_oneHundredTwentySevenDU_16001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 28699649617) ^ 14349824808 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 28699649617) ^ 9566549872 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 28699649617) ^ 2609059056 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 28699649617) ^ 667433712 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 28699649617) ^ 363286704 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 28699649617) ^ 1793616 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_31339037707 : Nat.Prime 31339037707 := by
  apply lucas_primality 31339037707 (14 : ZMod 31339037707)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (691, 1), (73387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (691, 1), (73387, 1)] : List FactorBlock).map factorBlockValue).prod) = 31339037707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_103
      · exact prime_oneHundredTwentySevenDU_691
      · exact prime_oneHundredTwentySevenDU_73387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 31339037707) ^ 15669518853 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (14 : ZMod 31339037707) ^ 10446345902 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (14 : ZMod 31339037707) ^ 304262502 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (14 : ZMod 31339037707) ^ 45353166 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (14 : ZMod 31339037707) ^ 427038 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_35220681887 : Nat.Prime 35220681887 := by
  apply lucas_primality 35220681887 (10 : ZMod 35220681887)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (5743, 1), (235877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (5743, 1), (235877, 1)] : List FactorBlock).map factorBlockValue).prod) = 35220681887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_5743
      · exact prime_oneHundredTwentySevenDU_235877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 35220681887) ^ 17610340943 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 35220681887) ^ 2709283222 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 35220681887) ^ 6132802 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 35220681887) ^ 149318 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_36073429069 : Nat.Prime 36073429069 := by
  apply lucas_primality 36073429069 (7 : ZMod 36073429069)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (50951171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (50951171, 1)] : List FactorBlock).map factorBlockValue).prod) = 36073429069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_59
      · exact prime_oneHundredTwentySevenDU_50951171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 36073429069) ^ 18036714534 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 36073429069) ^ 12024476356 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 36073429069) ^ 611414052 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 36073429069) ^ 708 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_37816137211 : Nat.Prime 37816137211 := by
  apply lucas_primality 37816137211 (3 : ZMod 37816137211)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (30744827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (30744827, 1)] : List FactorBlock).map factorBlockValue).prod) = 37816137211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_41
      · exact prime_oneHundredTwentySevenDU_30744827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37816137211) ^ 18908068605 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 37816137211) ^ 12605379070 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 37816137211) ^ 7563227442 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 37816137211) ^ 922344810 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 37816137211) ^ 1230 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_44778554789 : Nat.Prime 44778554789 := by
  apply lucas_primality 44778554789 (2 : ZMod 44778554789)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (14557, 1), (69911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (14557, 1), (69911, 1)] : List FactorBlock).map factorBlockValue).prod) = 44778554789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_14557
      · exact prime_oneHundredTwentySevenDU_69911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44778554789) ^ 22389277394 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44778554789) ^ 4070777708 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44778554789) ^ 3076084 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 44778554789) ^ 640508 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_47297525447 : Nat.Prime 47297525447 := by
  apply lucas_primality 47297525447 (5 : ZMod 47297525447)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11471, 1), (2061613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11471, 1), (2061613, 1)] : List FactorBlock).map factorBlockValue).prod) = 47297525447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11471
      · exact prime_oneHundredTwentySevenDU_2061613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 47297525447) ^ 23648762723 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 47297525447) ^ 4123226 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 47297525447) ^ 22942 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_52429538753 : Nat.Prime 52429538753 := by
  apply lucas_primality 52429538753 (3 : ZMod 52429538753)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (19, 1), (521, 1), (82757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (19, 1), (521, 1), (82757, 1)] : List FactorBlock).map factorBlockValue).prod) = 52429538753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_521
      · exact prime_oneHundredTwentySevenDU_82757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 52429538753) ^ 26214769376 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 52429538753) ^ 2759449408 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 52429538753) ^ 100632512 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 52429538753) ^ 633536 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_59028652493 : Nat.Prime 59028652493 := by
  apply lucas_primality 59028652493 (2 : ZMod 59028652493)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (14387, 1), (60337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (14387, 1), (60337, 1)] : List FactorBlock).map factorBlockValue).prod) = 59028652493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_14387
      · exact prime_oneHundredTwentySevenDU_60337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 59028652493) ^ 29514326246 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 59028652493) ^ 3472273676 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 59028652493) ^ 4102916 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 59028652493) ^ 978316 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_64381281071 : Nat.Prime 64381281071 := by
  apply lucas_primality 64381281071 (14 : ZMod 64381281071)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (191, 1), (977, 1), (34501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (191, 1), (977, 1), (34501, 1)] : List FactorBlock).map factorBlockValue).prod) = 64381281071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_191
      · exact prime_oneHundredTwentySevenDU_977
      · exact prime_oneHundredTwentySevenDU_34501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 64381281071) ^ 32190640535 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (14 : ZMod 64381281071) ^ 12876256214 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (14 : ZMod 64381281071) ^ 337074770 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (14 : ZMod 64381281071) ^ 65896910 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (14 : ZMod 64381281071) ^ 1866070 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_64619680691 : Nat.Prime 64619680691 := by
  apply lucas_primality 64619680691 (10 : ZMod 64619680691)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (787, 1), (8210887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (787, 1), (8210887, 1)] : List FactorBlock).map factorBlockValue).prod) = 64619680691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_787
      · exact prime_oneHundredTwentySevenDU_8210887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 64619680691) ^ 32309840345 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 64619680691) ^ 12923936138 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 64619680691) ^ 82108870 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 64619680691) ^ 7870 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_68966988941 : Nat.Prime 68966988941 := by
  apply lucas_primality 68966988941 (2 : ZMod 68966988941)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (79, 1), (3373, 1), (12941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (79, 1), (3373, 1), (12941, 1)] : List FactorBlock).map factorBlockValue).prod) = 68966988941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_79
      · exact prime_oneHundredTwentySevenDU_3373
      · exact prime_oneHundredTwentySevenDU_12941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68966988941) ^ 34483494470 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 68966988941) ^ 13793397788 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 68966988941) ^ 872999860 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 68966988941) ^ 20446780 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 68966988941) ^ 5329340 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_74660508983 : Nat.Prime 74660508983 := by
  apply lucas_primality 74660508983 (7 : ZMod 74660508983)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (109, 1), (20145847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (109, 1), (20145847, 1)] : List FactorBlock).map factorBlockValue).prod) = 74660508983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_109
      · exact prime_oneHundredTwentySevenDU_20145847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 74660508983) ^ 37330254491 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 74660508983) ^ 4391794646 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 74660508983) ^ 684958798 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 74660508983) ^ 3706 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_76422058751 : Nat.Prime 76422058751 := by
  apply lucas_primality 76422058751 (11 : ZMod 76422058751)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (47, 1), (607, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (47, 1), (607, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) = 76422058751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_47
      · exact prime_oneHundredTwentySevenDU_607
      · exact prime_oneHundredTwentySevenDU_2143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 76422058751) ^ 38211029375 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 76422058751) ^ 15284411750 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 76422058751) ^ 1626001250 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 76422058751) ^ 125901250 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 76422058751) ^ 35661250 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_90879251849 : Nat.Prime 90879251849 := by
  apply lucas_primality 90879251849 (3 : ZMod 90879251849)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (17, 1), (67, 1), (129527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (17, 1), (67, 1), (129527, 1)] : List FactorBlock).map factorBlockValue).prod) = 90879251849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_67
      · exact prime_oneHundredTwentySevenDU_129527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 90879251849) ^ 45439625924 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 90879251849) ^ 12982750264 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 90879251849) ^ 8261750168 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 90879251849) ^ 5345838344 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 90879251849) ^ 1356406744 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 90879251849) ^ 701624 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_92170049987 : Nat.Prime 92170049987 := by
  apply lucas_primality 92170049987 (2 : ZMod 92170049987)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (61, 1), (107927459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (61, 1), (107927459, 1)] : List FactorBlock).map factorBlockValue).prod) = 92170049987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_61
      · exact prime_oneHundredTwentySevenDU_107927459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 92170049987) ^ 46085024993 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 92170049987) ^ 13167149998 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 92170049987) ^ 1510984426 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 92170049987) ^ 854 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_111820243111 : Nat.Prime 111820243111 := by
  apply lucas_primality 111820243111 (3 : ZMod 111820243111)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (109, 1), (795251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (109, 1), (795251, 1)] : List FactorBlock).map factorBlockValue).prod) = 111820243111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_109
      · exact prime_oneHundredTwentySevenDU_795251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 111820243111) ^ 55910121555 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 111820243111) ^ 37273414370 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 111820243111) ^ 22364048622 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 111820243111) ^ 2600470770 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 111820243111) ^ 1025873790 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 111820243111) ^ 140610 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_120401494397 : Nat.Prime 120401494397 := by
  apply lucas_primality 120401494397 (2 : ZMod 120401494397)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (619, 1), (48627421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (619, 1), (48627421, 1)] : List FactorBlock).map factorBlockValue).prod) = 120401494397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_619
      · exact prime_oneHundredTwentySevenDU_48627421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 120401494397) ^ 60200747198 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 120401494397) ^ 194509684 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 120401494397) ^ 2476 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_128762562143 : Nat.Prime 128762562143 := by
  apply lucas_primality 128762562143 (5 : ZMod 128762562143)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (64381281071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (64381281071, 1)] : List FactorBlock).map factorBlockValue).prod) = 128762562143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_64381281071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 128762562143) ^ 64381281071 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 128762562143) ^ 2 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_131849483749 : Nat.Prime 131849483749 := by
  apply lucas_primality 131849483749 (2 : ZMod 131849483749)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (251, 1), (43774729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (251, 1), (43774729, 1)] : List FactorBlock).map factorBlockValue).prod) = 131849483749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_251
      · exact prime_oneHundredTwentySevenDU_43774729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 131849483749) ^ 65924741874 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131849483749) ^ 43949827916 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131849483749) ^ 525296748 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 131849483749) ^ 3012 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_151186778161 : Nat.Prime 151186778161 := by
  apply lucas_primality 151186778161 (7 : ZMod 151186778161)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (53, 1), (1080523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (53, 1), (1080523, 1)] : List FactorBlock).map factorBlockValue).prod) = 151186778161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_53
      · exact prime_oneHundredTwentySevenDU_1080523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 151186778161) ^ 75593389080 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 151186778161) ^ 50395592720 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 151186778161) ^ 30237355632 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 151186778161) ^ 13744252560 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 151186778161) ^ 2852580720 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 151186778161) ^ 139920 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_157920509293 : Nat.Prime 157920509293 := by
  apply lucas_primality 157920509293 (6 : ZMod 157920509293)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (47, 1), (3076933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (47, 1), (3076933, 1)] : List FactorBlock).map factorBlockValue).prod) = 157920509293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_47
      · exact prime_oneHundredTwentySevenDU_3076933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 157920509293) ^ 78960254646 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 157920509293) ^ 52640169764 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 157920509293) ^ 22560072756 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 157920509293) ^ 12147731484 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 157920509293) ^ 3360010836 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 157920509293) ^ 51324 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_174685172603 : Nat.Prime 174685172603 := by
  apply lucas_primality 174685172603 (2 : ZMod 174685172603)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (308631047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (308631047, 1)] : List FactorBlock).map factorBlockValue).prod) = 174685172603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_283
      · exact prime_oneHundredTwentySevenDU_308631047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 174685172603) ^ 87342586301 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 174685172603) ^ 617262094 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 174685172603) ^ 566 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_181654616669 : Nat.Prime 181654616669 := by
  apply lucas_primality 181654616669 (2 : ZMod 181654616669)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (47, 1), (907, 1), (152189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (47, 1), (907, 1), (152189, 1)] : List FactorBlock).map factorBlockValue).prod) = 181654616669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_47
      · exact prime_oneHundredTwentySevenDU_907
      · exact prime_oneHundredTwentySevenDU_152189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 181654616669) ^ 90827308334 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 181654616669) ^ 25950659524 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 181654616669) ^ 3864991844 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 181654616669) ^ 200280724 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 181654616669) ^ 1193612 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_202913518193 : Nat.Prime 202913518193 := by
  apply lucas_primality 202913518193 (3 : ZMod 202913518193)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (11, 1), (1847, 1), (12739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (11, 1), (1847, 1), (12739, 1)] : List FactorBlock).map factorBlockValue).prod) = 202913518193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_1847
      · exact prime_oneHundredTwentySevenDU_12739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 202913518193) ^ 101456759096 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 202913518193) ^ 28987645456 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 202913518193) ^ 18446683472 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 202913518193) ^ 109861136 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 202913518193) ^ 15928528 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_209407504421 : Nat.Prime 209407504421 := by
  apply lucas_primality 209407504421 (2 : ZMod 209407504421)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (57163, 1), (183167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (57163, 1), (183167, 1)] : List FactorBlock).map factorBlockValue).prod) = 209407504421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_57163
      · exact prime_oneHundredTwentySevenDU_183167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 209407504421) ^ 104703752210 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 209407504421) ^ 41881500884 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 209407504421) ^ 3663340 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 209407504421) ^ 1143260 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_218016322373 : Nat.Prime 218016322373 := by
  apply lucas_primality 218016322373 (2 : ZMod 218016322373)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (103, 1), (157, 1), (46171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (103, 1), (157, 1), (46171, 1)] : List FactorBlock).map factorBlockValue).prod) = 218016322373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_73
      · exact prime_oneHundredTwentySevenDU_103
      · exact prime_oneHundredTwentySevenDU_157
      · exact prime_oneHundredTwentySevenDU_46171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 218016322373) ^ 109008161186 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 218016322373) ^ 2986524964 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 218016322373) ^ 2116663324 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 218016322373) ^ 1388638996 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 218016322373) ^ 4721932 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_272119203431 : Nat.Prime 272119203431 := by
  apply lucas_primality 272119203431 (19 : ZMod 272119203431)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (151, 1), (180211393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (151, 1), (180211393, 1)] : List FactorBlock).map factorBlockValue).prod) = 272119203431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_151
      · exact prime_oneHundredTwentySevenDU_180211393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 272119203431) ^ 136059601715 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (19 : ZMod 272119203431) ^ 54423840686 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (19 : ZMod 272119203431) ^ 1802113930 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (19 : ZMod 272119203431) ^ 1510 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_300012461389 : Nat.Prime 300012461389 := by
  apply lucas_primality 300012461389 (2 : ZMod 300012461389)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (925964387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (925964387, 1)] : List FactorBlock).map factorBlockValue).prod) = 300012461389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_925964387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 300012461389) ^ 150006230694 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 300012461389) ^ 100004153796 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 300012461389) ^ 324 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_319425109789 : Nat.Prime 319425109789 := by
  apply lucas_primality 319425109789 (2 : ZMod 319425109789)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (26618759149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (26618759149, 1)] : List FactorBlock).map factorBlockValue).prod) = 319425109789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_26618759149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 319425109789) ^ 159712554894 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 319425109789) ^ 106475036596 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 319425109789) ^ 12 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_326559366059 : Nat.Prime 326559366059 := by
  apply lucas_primality 326559366059 (2 : ZMod 326559366059)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (9604687237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (9604687237, 1)] : List FactorBlock).map factorBlockValue).prod) = 326559366059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_9604687237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 326559366059) ^ 163279683029 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 326559366059) ^ 19209374474 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 326559366059) ^ 34 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_335282916907 : Nat.Prime 335282916907 := by
  apply lucas_primality 335282916907 (5 : ZMod 335282916907)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (331, 1), (8039201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (331, 1), (8039201, 1)] : List FactorBlock).map factorBlockValue).prod) = 335282916907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_331
      · exact prime_oneHundredTwentySevenDU_8039201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 335282916907) ^ 167641458453 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 335282916907) ^ 111760972302 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 335282916907) ^ 47897559558 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 335282916907) ^ 1012939326 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 335282916907) ^ 41706 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_356938944587 : Nat.Prime 356938944587 := by
  apply lucas_primality 356938944587 (2 : ZMod 356938944587)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (113, 1), (225625123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (113, 1), (225625123, 1)] : List FactorBlock).map factorBlockValue).prod) = 356938944587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_113
      · exact prime_oneHundredTwentySevenDU_225625123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 356938944587) ^ 178469472293 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 356938944587) ^ 50991277798 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 356938944587) ^ 3158751722 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 356938944587) ^ 1582 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_416563034933 : Nat.Prime 416563034933 := by
  apply lucas_primality 416563034933 (3 : ZMod 416563034933)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (107, 1), (1450489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (107, 1), (1450489, 1)] : List FactorBlock).map factorBlockValue).prod) = 416563034933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_61
      · exact prime_oneHundredTwentySevenDU_107
      · exact prime_oneHundredTwentySevenDU_1450489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 416563034933) ^ 208281517466 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 416563034933) ^ 37869366812 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 416563034933) ^ 6828902212 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 416563034933) ^ 3893112476 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 416563034933) ^ 287188 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_421664721103 : Nat.Prime 421664721103 := by
  apply lucas_primality 421664721103 (3 : ZMod 421664721103)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (53, 1), (107, 1), (217411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (53, 1), (107, 1), (217411, 1)] : List FactorBlock).map factorBlockValue).prod) = 421664721103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_53
      · exact prime_oneHundredTwentySevenDU_107
      · exact prime_oneHundredTwentySevenDU_217411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 421664721103) ^ 210832360551 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 421664721103) ^ 140554907034 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 421664721103) ^ 22192880058 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 421664721103) ^ 7955938134 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 421664721103) ^ 3940791786 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 421664721103) ^ 1939482 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_435166526413 : Nat.Prime 435166526413 := by
  apply lucas_primality 435166526413 (5 : ZMod 435166526413)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (227, 1), (5916769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (227, 1), (5916769, 1)] : List FactorBlock).map factorBlockValue).prod) = 435166526413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_227
      · exact prime_oneHundredTwentySevenDU_5916769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 435166526413) ^ 217583263206 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 435166526413) ^ 145055508804 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 435166526413) ^ 1917033156 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 435166526413) ^ 73548 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_560149211197 : Nat.Prime 560149211197 := by
  apply lucas_primality 560149211197 (2 : ZMod 560149211197)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (67, 1), (443, 1), (524231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (67, 1), (443, 1), (524231, 1)] : List FactorBlock).map factorBlockValue).prod) = 560149211197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_67
      · exact prime_oneHundredTwentySevenDU_443
      · exact prime_oneHundredTwentySevenDU_524231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 560149211197) ^ 280074605598 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 560149211197) ^ 186716403732 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 560149211197) ^ 8360435988 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 560149211197) ^ 1264445172 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 560149211197) ^ 1068516 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_657772415803 : Nat.Prime 657772415803 := by
  apply lucas_primality 657772415803 (3 : ZMod 657772415803)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (701, 1), (17376563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (701, 1), (17376563, 1)] : List FactorBlock).map factorBlockValue).prod) = 657772415803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_701
      · exact prime_oneHundredTwentySevenDU_17376563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 657772415803) ^ 328886207901 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 657772415803) ^ 219257471934 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 657772415803) ^ 938334402 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 657772415803) ^ 37854 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_678324458419 : Nat.Prime 678324458419 := by
  apply lucas_primality 678324458419 (2 : ZMod 678324458419)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1097, 1), (103057499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1097, 1), (103057499, 1)] : List FactorBlock).map factorBlockValue).prod) = 678324458419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_1097
      · exact prime_oneHundredTwentySevenDU_103057499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 678324458419) ^ 339162229209 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 678324458419) ^ 226108152806 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 678324458419) ^ 618344994 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 678324458419) ^ 6582 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_711698041387 : Nat.Prime 711698041387 := by
  apply lucas_primality 711698041387 (2 : ZMod 711698041387)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (491, 1), (26842349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (491, 1), (26842349, 1)] : List FactorBlock).map factorBlockValue).prod) = 711698041387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_491
      · exact prime_oneHundredTwentySevenDU_26842349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 711698041387) ^ 355849020693 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 711698041387) ^ 237232680462 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 711698041387) ^ 1449486846 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 711698041387) ^ 26514 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_860944894189 : Nat.Prime 860944894189 := by
  apply lucas_primality 860944894189 (2 : ZMod 860944894189)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (37, 1), (239, 1), (279767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (37, 1), (239, 1), (279767, 1)] : List FactorBlock).map factorBlockValue).prod) = 860944894189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_29
      · exact prime_oneHundredTwentySevenDU_37
      · exact prime_oneHundredTwentySevenDU_239
      · exact prime_oneHundredTwentySevenDU_279767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 860944894189) ^ 430472447094 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 860944894189) ^ 286981631396 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 860944894189) ^ 29687754972 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 860944894189) ^ 23268780924 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 860944894189) ^ 3602279892 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 860944894189) ^ 3077364 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_983407990783 : Nat.Prime 983407990783 := by
  apply lucas_primality 983407990783 (6 : ZMod 983407990783)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (43, 1), (544522697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (43, 1), (544522697, 1)] : List FactorBlock).map factorBlockValue).prod) = 983407990783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_544522697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 983407990783) ^ 491703995391 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 983407990783) ^ 327802663594 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 983407990783) ^ 140486855826 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 983407990783) ^ 22869953274 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 983407990783) ^ 1806 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1294661436613 : Nat.Prime 1294661436613 := by
  apply lucas_primality 1294661436613 (2 : ZMod 1294661436613)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1409, 1), (76570939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1409, 1), (76570939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1294661436613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_1409
      · exact prime_oneHundredTwentySevenDU_76570939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1294661436613) ^ 647330718306 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1294661436613) ^ 431553812204 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1294661436613) ^ 918851268 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1294661436613) ^ 16908 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1442715114641 : Nat.Prime 1442715114641 := by
  apply lucas_primality 1442715114641 (3 : ZMod 1442715114641)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (18033938933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (18033938933, 1)] : List FactorBlock).map factorBlockValue).prod) = 1442715114641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_18033938933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1442715114641) ^ 721357557320 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1442715114641) ^ 288543022928 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1442715114641) ^ 80 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1483834635403 : Nat.Prime 1483834635403 := by
  apply lucas_primality 1483834635403 (2 : ZMod 1483834635403)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (19, 1), (265634557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (19, 1), (265634557, 1)] : List FactorBlock).map factorBlockValue).prod) = 1483834635403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_265634557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1483834635403) ^ 741917317701 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483834635403) ^ 494611545134 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483834635403) ^ 211976376486 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483834635403) ^ 78096559758 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1483834635403) ^ 5586 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1642560307711 : Nat.Prime 1642560307711 := by
  apply lucas_primality 1642560307711 (3 : ZMod 1642560307711)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (127, 1), (1664549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (37, 1), (127, 1), (1664549, 1)] : List FactorBlock).map factorBlockValue).prod) = 1642560307711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_37
      · exact prime_oneHundredTwentySevenDU_127
      · exact prime_oneHundredTwentySevenDU_1664549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1642560307711) ^ 821280153855 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1642560307711) ^ 547520102570 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1642560307711) ^ 328512061542 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1642560307711) ^ 234651472530 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1642560307711) ^ 44393521830 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1642560307711) ^ 12933545730 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1642560307711) ^ 986790 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1661269549229 : Nat.Prime 1661269549229 := by
  apply lucas_primality 1661269549229 (2 : ZMod 1661269549229)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (53, 1), (8623, 1), (39511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (53, 1), (8623, 1), (39511, 1)] : List FactorBlock).map factorBlockValue).prod) = 1661269549229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_23
      · exact prime_oneHundredTwentySevenDU_53
      · exact prime_oneHundredTwentySevenDU_8623
      · exact prime_oneHundredTwentySevenDU_39511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1661269549229) ^ 830634774614 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1661269549229) ^ 72229110836 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1661269549229) ^ 31344708476 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1661269549229) ^ 192655636 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1661269549229) ^ 42045748 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1932162287527 : Nat.Prime 1932162287527 := by
  apply lucas_primality 1932162287527 (3 : ZMod 1932162287527)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (25589, 1), (4194863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (25589, 1), (4194863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1932162287527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_25589
      · exact prime_oneHundredTwentySevenDU_4194863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1932162287527) ^ 966081143763 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932162287527) ^ 644054095842 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932162287527) ^ 75507534 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932162287527) ^ 460602 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_2470424681537 : Nat.Prime 2470424681537 := by
  apply lucas_primality 2470424681537 (3 : ZMod 2470424681537)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (29, 1), (190149683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (29, 1), (190149683, 1)] : List FactorBlock).map factorBlockValue).prod) = 2470424681537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_29
      · exact prime_oneHundredTwentySevenDU_190149683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2470424681537) ^ 1235212340768 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2470424681537) ^ 352917811648 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2470424681537) ^ 85187057984 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2470424681537) ^ 12992 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_2667475776943 : Nat.Prime 2667475776943 := by
  apply lucas_primality 2667475776943 (3 : ZMod 2667475776943)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (43, 1), (1148783711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (43, 1), (1148783711, 1)] : List FactorBlock).map factorBlockValue).prod) = 2667475776943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_1148783711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2667475776943) ^ 1333737888471 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2667475776943) ^ 889158592314 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2667475776943) ^ 62034320394 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2667475776943) ^ 2322 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_4195077308707 : Nat.Prime 4195077308707 := by
  apply lucas_primality 4195077308707 (2 : ZMod 4195077308707)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (15017, 1), (589357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (15017, 1), (589357, 1)] : List FactorBlock).map factorBlockValue).prod) = 4195077308707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_79
      · exact prime_oneHundredTwentySevenDU_15017
      · exact prime_oneHundredTwentySevenDU_589357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4195077308707) ^ 2097538654353 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4195077308707) ^ 1398359102902 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4195077308707) ^ 53102244414 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4195077308707) ^ 279355218 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4195077308707) ^ 7118058 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_4397852289839 : Nat.Prime 4397852289839 := by
  apply lucas_primality 4397852289839 (7 : ZMod 4397852289839)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (10133300207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (10133300207, 1)] : List FactorBlock).map factorBlockValue).prod) = 4397852289839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_31
      · exact prime_oneHundredTwentySevenDU_10133300207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4397852289839) ^ 2198926144919 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4397852289839) ^ 628264612834 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4397852289839) ^ 141866202898 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 4397852289839) ^ 434 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_4879142104181 : Nat.Prime 4879142104181 := by
  apply lucas_primality 4879142104181 (2 : ZMod 4879142104181)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (7869584039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (7869584039, 1)] : List FactorBlock).map factorBlockValue).prod) = 4879142104181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_31
      · exact prime_oneHundredTwentySevenDU_7869584039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4879142104181) ^ 2439571052090 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4879142104181) ^ 975828420836 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4879142104181) ^ 157391680780 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 4879142104181) ^ 620 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_5240555178091 : Nat.Prime 5240555178091 := by
  apply lucas_primality 5240555178091 (10 : ZMod 5240555178091)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (174685172603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (174685172603, 1)] : List FactorBlock).map factorBlockValue).prod) = 5240555178091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_174685172603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 5240555178091) ^ 2620277589045 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 5240555178091) ^ 1746851726030 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 5240555178091) ^ 1048111035618 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 5240555178091) ^ 30 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_6054083257217 : Nat.Prime 6054083257217 := by
  apply lucas_primality 6054083257217 (3 : ZMod 6054083257217)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (47297525447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (47297525447, 1)] : List FactorBlock).map factorBlockValue).prod) = 6054083257217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_47297525447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 6054083257217) ^ 3027041628608 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 6054083257217) ^ 128 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_7370799759437 : Nat.Prime 7370799759437 := by
  apply lucas_primality 7370799759437 (2 : ZMod 7370799759437)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (67, 1), (1061, 1), (1364303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (67, 1), (1061, 1), (1364303, 1)] : List FactorBlock).map factorBlockValue).prod) = 7370799759437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_67
      · exact prime_oneHundredTwentySevenDU_1061
      · exact prime_oneHundredTwentySevenDU_1364303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7370799759437) ^ 3685399879718 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7370799759437) ^ 387936829444 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7370799759437) ^ 110011936708 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7370799759437) ^ 6947030876 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7370799759437) ^ 5402612 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_8983825017619 : Nat.Prime 8983825017619 := by
  apply lucas_primality 8983825017619 (2 : ZMod 8983825017619)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (151, 1), (53026319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (151, 1), (53026319, 1)] : List FactorBlock).map factorBlockValue).prod) = 8983825017619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_151
      · exact prime_oneHundredTwentySevenDU_53026319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8983825017619) ^ 4491912508809 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8983825017619) ^ 2994608339206 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8983825017619) ^ 816711365238 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8983825017619) ^ 528460295154 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8983825017619) ^ 59495529918 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 8983825017619) ^ 169422 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_11605226786521 : Nat.Prime 11605226786521 := by
  apply lucas_primality 11605226786521 (41 : ZMod 11605226786521)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (661, 1), (146308961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (661, 1), (146308961, 1)] : List FactorBlock).map factorBlockValue).prod) = 11605226786521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_661
      · exact prime_oneHundredTwentySevenDU_146308961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (41 : ZMod 11605226786521) ^ 5802613393260 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (41 : ZMod 11605226786521) ^ 3868408928840 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (41 : ZMod 11605226786521) ^ 2321045357304 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (41 : ZMod 11605226786521) ^ 17557075320 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (41 : ZMod 11605226786521) ^ 79320 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_13720507840183 : Nat.Prime 13720507840183 := by
  apply lucas_primality 13720507840183 (6 : ZMod 13720507840183)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (367, 1), (43572937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (367, 1), (43572937, 1)] : List FactorBlock).map factorBlockValue).prod) = 13720507840183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_367
      · exact prime_oneHundredTwentySevenDU_43572937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 13720507840183) ^ 6860253920091 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 13720507840183) ^ 4573502613394 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 13720507840183) ^ 1247318894562 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 13720507840183) ^ 1055423680014 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 13720507840183) ^ 37385579946 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 13720507840183) ^ 314886 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_13904432151769 : Nat.Prime 13904432151769 := by
  apply lucas_primality 13904432151769 (7 : ZMod 13904432151769)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (1901, 1), (3221, 1), (10513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (1901, 1), (3221, 1), (10513, 1)] : List FactorBlock).map factorBlockValue).prod) = 13904432151769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_1901
      · exact prime_oneHundredTwentySevenDU_3221
      · exact prime_oneHundredTwentySevenDU_10513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13904432151769) ^ 6952216075884 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 13904432151769) ^ 4634810717256 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 13904432151769) ^ 7314272568 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 13904432151769) ^ 4316806008 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 13904432151769) ^ 1322594136 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_18435090831041 : Nat.Prime 18435090831041 := by
  apply lucas_primality 18435090831041 (3 : ZMod 18435090831041)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (13, 1), (127, 1), (34893797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (13, 1), (127, 1), (34893797, 1)] : List FactorBlock).map factorBlockValue).prod) = 18435090831041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_127
      · exact prime_oneHundredTwentySevenDU_34893797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18435090831041) ^ 9217545415520 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 18435090831041) ^ 3687018166208 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 18435090831041) ^ 1418083910080 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 18435090831041) ^ 145158195520 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 18435090831041) ^ 528320 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_20714582985809 : Nat.Prime 20714582985809 := by
  apply lucas_primality 20714582985809 (3 : ZMod 20714582985809)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1294661436613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1294661436613, 1)] : List FactorBlock).map factorBlockValue).prod) = 20714582985809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_1294661436613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 20714582985809) ^ 10357291492904 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 20714582985809) ^ 16 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_28502910546241 : Nat.Prime 28502910546241 := by
  apply lucas_primality 28502910546241 (7 : ZMod 28502910546241)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (13, 1), (45137, 1), (50599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (13, 1), (45137, 1), (50599, 1)] : List FactorBlock).map factorBlockValue).prod) = 28502910546241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_45137
      · exact prime_oneHundredTwentySevenDU_50599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 28502910546241) ^ 14251455273120 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 28502910546241) ^ 9500970182080 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 28502910546241) ^ 5700582109248 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 28502910546241) ^ 2192531580480 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 28502910546241) ^ 631475520 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 28502910546241) ^ 563309760 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_40074594091901 : Nat.Prime 40074594091901 := by
  apply lucas_primality 40074594091901 (3 : ZMod 40074594091901)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (353, 1), (1135257623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (353, 1), (1135257623, 1)] : List FactorBlock).map factorBlockValue).prod) = 40074594091901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_353
      · exact prime_oneHundredTwentySevenDU_1135257623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40074594091901) ^ 20037297045950 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 40074594091901) ^ 8014918818380 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 40074594091901) ^ 113525762300 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 40074594091901) ^ 35300 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_42577871126981 : Nat.Prime 42577871126981 := by
  apply lucas_primality 42577871126981 (13 : ZMod 42577871126981)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (353, 1), (861551419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (353, 1), (861551419, 1)] : List FactorBlock).map factorBlockValue).prod) = 42577871126981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_353
      · exact prime_oneHundredTwentySevenDU_861551419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 42577871126981) ^ 21288935563490 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 42577871126981) ^ 8515574225396 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 42577871126981) ^ 6082553018140 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 42577871126981) ^ 120617198660 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 42577871126981) ^ 49420 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_54611142222487 : Nat.Prime 54611142222487 := by
  apply lucas_primality 54611142222487 (3 : ZMod 54611142222487)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1811, 1), (3911, 1), (1285061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1811, 1), (3911, 1), (1285061, 1)] : List FactorBlock).map factorBlockValue).prod) = 54611142222487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_1811
      · exact prime_oneHundredTwentySevenDU_3911
      · exact prime_oneHundredTwentySevenDU_1285061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 54611142222487) ^ 27305571111243 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 54611142222487) ^ 18203714074162 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 54611142222487) ^ 30155241426 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 54611142222487) ^ 13963472826 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 54611142222487) ^ 42496926 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_64019418646633 : Nat.Prime 64019418646633 := by
  apply lucas_primality 64019418646633 (5 : ZMod 64019418646633)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2667475776943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2667475776943, 1)] : List FactorBlock).map factorBlockValue).prod) = 64019418646633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_2667475776943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 64019418646633) ^ 32009709323316 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 64019418646633) ^ 21339806215544 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 64019418646633) ^ 24 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_73388465134277 : Nat.Prime 73388465134277 := by
  apply lucas_primality 73388465134277 (2 : ZMod 73388465134277)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (181654616669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (181654616669, 1)] : List FactorBlock).map factorBlockValue).prod) = 73388465134277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_101
      · exact prime_oneHundredTwentySevenDU_181654616669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 73388465134277) ^ 36694232567138 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 73388465134277) ^ 726618466676 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 73388465134277) ^ 404 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_78716468506589 : Nat.Prime 78716468506589 := by
  apply lucas_primality 78716468506589 (2 : ZMod 78716468506589)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (97, 1), (1297, 1), (1847, 1), (7699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (97, 1), (1297, 1), (1847, 1), (7699, 1)] : List FactorBlock).map factorBlockValue).prod) = 78716468506589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_97
      · exact prime_oneHundredTwentySevenDU_1297
      · exact prime_oneHundredTwentySevenDU_1847
      · exact prime_oneHundredTwentySevenDU_7699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78716468506589) ^ 39358234253294 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78716468506589) ^ 7156042591508 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78716468506589) ^ 811509984604 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78716468506589) ^ 60691186204 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78716468506589) ^ 42618553604 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78716468506589) ^ 10224245812 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_98665862370451 : Nat.Prime 98665862370451 := by
  apply lucas_primality 98665862370451 (10 : ZMod 98665862370451)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (657772415803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (657772415803, 1)] : List FactorBlock).map factorBlockValue).prod) = 98665862370451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_657772415803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 98665862370451) ^ 49332931185225 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 98665862370451) ^ 32888620790150 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 98665862370451) ^ 19733172474090 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 98665862370451) ^ 150 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_99199268138041 : Nat.Prime 99199268138041 := by
  apply lucas_primality 99199268138041 (13 : ZMod 99199268138041)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 3), (2410089119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 3), (2410089119, 1)] : List FactorBlock).map factorBlockValue).prod) = 99199268138041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_2410089119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 99199268138041) ^ 49599634069020 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 99199268138041) ^ 33066422712680 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 99199268138041) ^ 19839853627608 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 99199268138041) ^ 14171324019720 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 99199268138041) ^ 41160 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_103890515300333 : Nat.Prime 103890515300333 := by
  apply lucas_primality 103890515300333 (2 : ZMod 103890515300333)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (691, 1), (1153, 1), (1051591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (691, 1), (1153, 1), (1051591, 1)] : List FactorBlock).map factorBlockValue).prod) = 103890515300333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_31
      · exact prime_oneHundredTwentySevenDU_691
      · exact prime_oneHundredTwentySevenDU_1153
      · exact prime_oneHundredTwentySevenDU_1051591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 103890515300333) ^ 51945257650166 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103890515300333) ^ 3351306945172 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103890515300333) ^ 150348068452 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103890515300333) ^ 90104523244 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 103890515300333) ^ 98793652 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_113518521745283 : Nat.Prime 113518521745283 := by
  apply lucas_primality 113518521745283 (2 : ZMod 113518521745283)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (769, 1), (1091, 1), (67652779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (769, 1), (1091, 1), (67652779, 1)] : List FactorBlock).map factorBlockValue).prod) = 113518521745283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_769
      · exact prime_oneHundredTwentySevenDU_1091
      · exact prime_oneHundredTwentySevenDU_67652779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113518521745283) ^ 56759260872641 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 113518521745283) ^ 147618363778 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 113518521745283) ^ 104049974102 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 113518521745283) ^ 1677958 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_210594733596833 : Nat.Prime 210594733596833 := by
  apply lucas_primality 210594733596833 (3 : ZMod 210594733596833)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (17, 1), (29, 2), (3877, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (17, 1), (29, 2), (3877, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) = 210594733596833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_29
      · exact prime_oneHundredTwentySevenDU_3877
      · exact prime_oneHundredTwentySevenDU_9133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 210594733596833) ^ 105297366798416 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 210594733596833) ^ 16199594892064 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 210594733596833) ^ 12387925505696 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 210594733596833) ^ 7261887365408 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 210594733596833) ^ 54318992416 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 210594733596833) ^ 23058659104 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_230194123331209 : Nat.Prime 230194123331209 := by
  apply lucas_primality 230194123331209 (13 : ZMod 230194123331209)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (109, 1), (269, 1), (4159, 1), (78653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (109, 1), (269, 1), (4159, 1), (78653, 1)] : List FactorBlock).map factorBlockValue).prod) = 230194123331209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_109
      · exact prime_oneHundredTwentySevenDU_269
      · exact prime_oneHundredTwentySevenDU_4159
      · exact prime_oneHundredTwentySevenDU_78653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 230194123331209) ^ 115097061665604 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 230194123331209) ^ 76731374443736 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 230194123331209) ^ 2111872691112 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 230194123331209) ^ 855740235432 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 230194123331209) ^ 55348430712 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 230194123331209) ^ 2926704936 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_248574995829709 : Nat.Prime 248574995829709 := by
  apply lucas_primality 248574995829709 (2 : ZMod 248574995829709)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (20714582985809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (20714582985809, 1)] : List FactorBlock).map factorBlockValue).prod) = 248574995829709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_20714582985809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 248574995829709) ^ 124287497914854 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 248574995829709) ^ 82858331943236 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 248574995829709) ^ 12 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_274750864424423 : Nat.Prime 274750864424423 := by
  apply lucas_primality 274750864424423 (5 : ZMod 274750864424423)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5711411, 1), (24052801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5711411, 1), (24052801, 1)] : List FactorBlock).map factorBlockValue).prod) = 274750864424423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5711411
      · exact prime_oneHundredTwentySevenDU_24052801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 274750864424423) ^ 137375432212211 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 274750864424423) ^ 48105602 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 274750864424423) ^ 11422822 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_277007111612593 : Nat.Prime 277007111612593 := by
  apply lucas_primality 277007111612593 (5 : ZMod 277007111612593)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1507091, 1), (3829219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1507091, 1), (3829219, 1)] : List FactorBlock).map factorBlockValue).prod) = 277007111612593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_1507091
      · exact prime_oneHundredTwentySevenDU_3829219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 277007111612593) ^ 138503555806296 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 277007111612593) ^ 92335703870864 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 277007111612593) ^ 183802512 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 277007111612593) ^ 72340368 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_395574488127869 : Nat.Prime 395574488127869 := by
  apply lucas_primality 395574488127869 (2 : ZMod 395574488127869)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1541209, 1), (9166609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1541209, 1), (9166609, 1)] : List FactorBlock).map factorBlockValue).prod) = 395574488127869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_1541209
      · exact prime_oneHundredTwentySevenDU_9166609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 395574488127869) ^ 197787244063934 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 395574488127869) ^ 56510641161124 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 395574488127869) ^ 256665052 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 395574488127869) ^ 43153852 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_581928790317139 : Nat.Prime 581928790317139 := by
  apply lucas_primality 581928790317139 (2 : ZMod 581928790317139)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (11, 1), (326559366059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (11, 1), (326559366059, 1)] : List FactorBlock).map factorBlockValue).prod) = 581928790317139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_326559366059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 581928790317139) ^ 290964395158569 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 581928790317139) ^ 193976263439046 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 581928790317139) ^ 52902617301558 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 581928790317139) ^ 1782 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_879898601603851 : Nat.Prime 879898601603851 := by
  apply lucas_primality 879898601603851 (2 : ZMod 879898601603851)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (131, 1), (44778554789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (131, 1), (44778554789, 1)] : List FactorBlock).map factorBlockValue).prod) = 879898601603851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_131
      · exact prime_oneHundredTwentySevenDU_44778554789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 879898601603851) ^ 439949300801925 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 879898601603851) ^ 293299533867950 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 879898601603851) ^ 175979720320770 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 879898601603851) ^ 6716783218350 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 879898601603851) ^ 19650 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1478658753589873 : Nat.Prime 1478658753589873 := by
  apply lucas_primality 1478658753589873 (5 : ZMod 1478658753589873)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (245339, 1), (125562551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (245339, 1), (125562551, 1)] : List FactorBlock).map factorBlockValue).prod) = 1478658753589873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_245339
      · exact prime_oneHundredTwentySevenDU_125562551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1478658753589873) ^ 739329376794936 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1478658753589873) ^ 492886251196624 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1478658753589873) ^ 6027002448 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 1478658753589873) ^ 11776272 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1710272108793769 : Nat.Prime 1710272108793769 := by
  apply lucas_primality 1710272108793769 (7 : ZMod 1710272108793769)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 2), (421664721103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 2), (421664721103, 1)] : List FactorBlock).map factorBlockValue).prod) = 1710272108793769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_421664721103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1710272108793769) ^ 855136054396884 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1710272108793769) ^ 570090702931256 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1710272108793769) ^ 131559392984136 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 1710272108793769) ^ 4056 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_2674112605937369 : Nat.Prime 2674112605937369 := by
  apply lucas_primality 2674112605937369 (3 : ZMod 2674112605937369)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (173, 1), (1932162287527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (173, 1), (1932162287527, 1)] : List FactorBlock).map factorBlockValue).prod) = 2674112605937369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_173
      · exact prime_oneHundredTwentySevenDU_1932162287527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2674112605937369) ^ 1337056302968684 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2674112605937369) ^ 15457298300216 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2674112605937369) ^ 1384 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_2684131010758039 : Nat.Prime 2684131010758039 := by
  apply lucas_primality 2684131010758039 (6 : ZMod 2684131010758039)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113489, 1), (3941837257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113489, 1), (3941837257, 1)] : List FactorBlock).map factorBlockValue).prod) = 2684131010758039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_113489
      · exact prime_oneHundredTwentySevenDU_3941837257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2684131010758039) ^ 1342065505379019 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 2684131010758039) ^ 894710336919346 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 2684131010758039) ^ 23651023542 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 2684131010758039) ^ 680934 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_3746710295723321 : Nat.Prime 3746710295723321 := by
  apply lucas_primality 3746710295723321 (6 : ZMod 3746710295723321)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 3), (29, 1), (1039, 1), (453227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 3), (29, 1), (1039, 1), (453227, 1)] : List FactorBlock).map factorBlockValue).prod) = 3746710295723321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_29
      · exact prime_oneHundredTwentySevenDU_1039
      · exact prime_oneHundredTwentySevenDU_453227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3746710295723321) ^ 1873355147861660 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3746710295723321) ^ 749342059144664 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3746710295723321) ^ 197195278722280 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3746710295723321) ^ 129196906749080 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3746710295723321) ^ 3606073431880 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 3746710295723321) ^ 8266741160 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_4024753607893313 : Nat.Prime 4024753607893313 := by
  apply lucas_primality 4024753607893313 (3 : ZMod 4024753607893313)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (8983825017619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (8983825017619, 1)] : List FactorBlock).map factorBlockValue).prod) = 4024753607893313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_8983825017619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4024753607893313) ^ 2012376803946656 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4024753607893313) ^ 574964801127616 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4024753607893313) ^ 448 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_4356319647302383 : Nat.Prime 4356319647302383 := by
  apply lucas_primality 4356319647302383 (3 : ZMod 4356319647302383)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2273, 1), (319425109789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2273, 1), (319425109789, 1)] : List FactorBlock).map factorBlockValue).prod) = 4356319647302383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_2273
      · exact prime_oneHundredTwentySevenDU_319425109789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4356319647302383) ^ 2178159823651191 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4356319647302383) ^ 1452106549100794 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4356319647302383) ^ 1916550658734 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 4356319647302383) ^ 13638 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_4829146915235473 : Nat.Prime 4829146915235473 := by
  apply lucas_primality 4829146915235473 (5 : ZMod 4829146915235473)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (23, 1), (142007, 1), (10267633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (23, 1), (142007, 1), (10267633, 1)] : List FactorBlock).map factorBlockValue).prod) = 4829146915235473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_23
      · exact prime_oneHundredTwentySevenDU_142007
      · exact prime_oneHundredTwentySevenDU_10267633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4829146915235473) ^ 2414573457617736 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4829146915235473) ^ 1609715638411824 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4829146915235473) ^ 209962909358064 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4829146915235473) ^ 34006400496 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 4829146915235473) ^ 470327184 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_4918956311646719 : Nat.Prime 4918956311646719 := by
  apply lucas_primality 4918956311646719 (11 : ZMod 4918956311646719)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (383, 1), (738421, 1), (790583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (383, 1), (738421, 1), (790583, 1)] : List FactorBlock).map factorBlockValue).prod) = 4918956311646719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_383
      · exact prime_oneHundredTwentySevenDU_738421
      · exact prime_oneHundredTwentySevenDU_790583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4918956311646719) ^ 2459478155823359 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 4918956311646719) ^ 447177846513338 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 4918956311646719) ^ 12843227967746 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 4918956311646719) ^ 6661452358 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (11 : ZMod 4918956311646719) ^ 6221935346 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_7142347305938953 : Nat.Prime 7142347305938953 := by
  apply lucas_primality 7142347305938953 (5 : ZMod 7142347305938953)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (99199268138041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (99199268138041, 1)] : List FactorBlock).map factorBlockValue).prod) = 7142347305938953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_99199268138041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7142347305938953) ^ 3571173652969476 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7142347305938953) ^ 2380782435312984 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 7142347305938953) ^ 72 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_8232702527553487 : Nat.Prime 8232702527553487 := by
  apply lucas_primality 8232702527553487 (3 : ZMod 8232702527553487)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43783, 1), (31339037707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43783, 1), (31339037707, 1)] : List FactorBlock).map factorBlockValue).prod) = 8232702527553487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_43783
      · exact prime_oneHundredTwentySevenDU_31339037707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8232702527553487) ^ 4116351263776743 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 8232702527553487) ^ 2744234175851162 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 8232702527553487) ^ 188034226242 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 8232702527553487) ^ 262698 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_14132123075388491 : Nat.Prime 14132123075388491 := by
  apply lucas_primality 14132123075388491 (2 : ZMod 14132123075388491)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (103, 1), (13720507840183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (103, 1), (13720507840183, 1)] : List FactorBlock).map factorBlockValue).prod) = 14132123075388491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_103
      · exact prime_oneHundredTwentySevenDU_13720507840183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14132123075388491) ^ 7066061537694245 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14132123075388491) ^ 2826424615077698 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14132123075388491) ^ 137205078401830 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14132123075388491) ^ 1030 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_15343203451594771 : Nat.Prime 15343203451594771 := by
  apply lucas_primality 15343203451594771 (2 : ZMod 15343203451594771)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (56087, 1), (1013188073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (56087, 1), (1013188073, 1)] : List FactorBlock).map factorBlockValue).prod) = 15343203451594771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_56087
      · exact prime_oneHundredTwentySevenDU_1013188073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15343203451594771) ^ 7671601725797385 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15343203451594771) ^ 5114401150531590 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15343203451594771) ^ 3068640690318954 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15343203451594771) ^ 273560779710 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 15343203451594771) ^ 15143490 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_15800296222924051 : Nat.Prime 15800296222924051 := by
  apply lucas_primality 15800296222924051 (3 : ZMod 15800296222924051)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (16487, 1), (6388991821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (16487, 1), (6388991821, 1)] : List FactorBlock).map factorBlockValue).prod) = 15800296222924051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_16487
      · exact prime_oneHundredTwentySevenDU_6388991821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15800296222924051) ^ 7900148111462025 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15800296222924051) ^ 5266765407641350 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15800296222924051) ^ 3160059244584810 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15800296222924051) ^ 958348773150 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15800296222924051) ^ 2473050 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_22274850793972289 : Nat.Prime 22274850793972289 := by
  apply lucas_primality 22274850793972289 (3 : ZMod 22274850793972289)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (59, 1), (241, 1), (7417, 1), (3300179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (59, 1), (241, 1), (7417, 1), (3300179, 1)] : List FactorBlock).map factorBlockValue).prod) = 22274850793972289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_59
      · exact prime_oneHundredTwentySevenDU_241
      · exact prime_oneHundredTwentySevenDU_7417
      · exact prime_oneHundredTwentySevenDU_3300179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22274850793972289) ^ 11137425396986144 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 22274850793972289) ^ 377539843965632 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 22274850793972289) ^ 92426766779968 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 22274850793972289) ^ 3003215692864 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 22274850793972289) ^ 6749588672 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_23384815479528299 : Nat.Prime 23384815479528299 := by
  apply lucas_primality 23384815479528299 (2 : ZMod 23384815479528299)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (113518521745283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (113518521745283, 1)] : List FactorBlock).map factorBlockValue).prod) = 23384815479528299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_103
      · exact prime_oneHundredTwentySevenDU_113518521745283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23384815479528299) ^ 11692407739764149 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 23384815479528299) ^ 227037043490566 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 23384815479528299) ^ 206 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_23832009159108889 : Nat.Prime 23832009159108889 := by
  apply lucas_primality 23832009159108889 (13 : ZMod 23832009159108889)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (131687, 1), (7540610551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (131687, 1), (7540610551, 1)] : List FactorBlock).map factorBlockValue).prod) = 23832009159108889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_131687
      · exact prime_oneHundredTwentySevenDU_7540610551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 23832009159108889) ^ 11916004579554444 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 23832009159108889) ^ 7944003053036296 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 23832009159108889) ^ 180974653224 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (13 : ZMod 23832009159108889) ^ 3160488 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_27932581935222673 : Nat.Prime 27932581935222673 := by
  apply lucas_primality 27932581935222673 (5 : ZMod 27932581935222673)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (581928790317139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (581928790317139, 1)] : List FactorBlock).map factorBlockValue).prod) = 27932581935222673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_581928790317139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 27932581935222673) ^ 13966290967611336 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 27932581935222673) ^ 9310860645074224 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 27932581935222673) ^ 48 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_47204832228698357 : Nat.Prime 47204832228698357 := by
  apply lucas_primality 47204832228698357 (2 : ZMod 47204832228698357)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1861, 1), (434293, 1), (14601493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1861, 1), (434293, 1), (14601493, 1)] : List FactorBlock).map factorBlockValue).prod) = 47204832228698357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_1861
      · exact prime_oneHundredTwentySevenDU_434293
      · exact prime_oneHundredTwentySevenDU_14601493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47204832228698357) ^ 23602416114349178 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 47204832228698357) ^ 25365304797796 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 47204832228698357) ^ 108693513892 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 47204832228698357) ^ 3232877092 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_71763535232472623 : Nat.Prime 71763535232472623 := by
  apply lucas_primality 71763535232472623 (7 : ZMod 71763535232472623)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (17, 1), (19, 1), (1442715114641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (17, 1), (19, 1), (1442715114641, 1)] : List FactorBlock).map factorBlockValue).prod) = 71763535232472623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_1442715114641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 71763535232472623) ^ 35881767616236311 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 71763535232472623) ^ 10251933604638946 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 71763535232472623) ^ 6523957748406602 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 71763535232472623) ^ 4221384425439566 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 71763535232472623) ^ 3777028170130138 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 71763535232472623) ^ 49742 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_81980158691670443 : Nat.Prime 81980158691670443 := by
  apply lucas_primality 81980158691670443 (2 : ZMod 81980158691670443)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (9619, 1), (258101, 1), (2358637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (9619, 1), (258101, 1), (2358637, 1)] : List FactorBlock).map factorBlockValue).prod) = 81980158691670443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_9619
      · exact prime_oneHundredTwentySevenDU_258101
      · exact prime_oneHundredTwentySevenDU_2358637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 81980158691670443) ^ 40990079345835221 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 81980158691670443) ^ 11711451241667206 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 81980158691670443) ^ 8522731956718 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 81980158691670443) ^ 317628210242 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 81980158691670443) ^ 34757429266 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_84659036714490673 : Nat.Prime 84659036714490673 := by
  apply lucas_primality 84659036714490673 (10 : ZMod 84659036714490673)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (193, 1), (435166526413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (193, 1), (435166526413, 1)] : List FactorBlock).map factorBlockValue).prod) = 84659036714490673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_193
      · exact prime_oneHundredTwentySevenDU_435166526413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 84659036714490673) ^ 42329518357245336 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 84659036714490673) ^ 28219678904830224 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 84659036714490673) ^ 12094148102070096 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 84659036714490673) ^ 438647858624304 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (10 : ZMod 84659036714490673) ^ 194544 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_226537375929278693 : Nat.Prime 226537375929278693 := by
  apply lucas_primality 226537375929278693 (2 : ZMod 226537375929278693)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (223, 1), (457, 1), (19162881467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (223, 1), (457, 1), (19162881467, 1)] : List FactorBlock).map factorBlockValue).prod) = 226537375929278693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_29
      · exact prime_oneHundredTwentySevenDU_223
      · exact prime_oneHundredTwentySevenDU_457
      · exact prime_oneHundredTwentySevenDU_19162881467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 226537375929278693) ^ 113268687964639346 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 226537375929278693) ^ 7811633652733748 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 226537375929278693) ^ 1015862672328604 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 226537375929278693) ^ 495705417788356 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 226537375929278693) ^ 11821676 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_234575238662144707 : Nat.Prime 234575238662144707 := by
  apply lucas_primality 234575238662144707 (2 : ZMod 234575238662144707)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1033841, 1), (37816137211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1033841, 1), (37816137211, 1)] : List FactorBlock).map factorBlockValue).prod) = 234575238662144707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_1033841
      · exact prime_oneHundredTwentySevenDU_37816137211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 234575238662144707) ^ 117287619331072353 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 234575238662144707) ^ 78191746220714902 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 234575238662144707) ^ 226896823266 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 234575238662144707) ^ 6203046 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_241279857573061289 : Nat.Prime 241279857573061289 := by
  apply lucas_primality 241279857573061289 (3 : ZMod 241279857573061289)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2581097, 1), (11684947213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2581097, 1), (11684947213, 1)] : List FactorBlock).map factorBlockValue).prod) = 241279857573061289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_2581097
      · exact prime_oneHundredTwentySevenDU_11684947213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 241279857573061289) ^ 120639928786530644 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 241279857573061289) ^ 93479577704 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 241279857573061289) ^ 20648776 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_513318325004412779 : Nat.Prime 513318325004412779 := by
  apply lucas_primality 513318325004412779 (2 : ZMod 513318325004412779)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (173, 1), (641, 1), (74660508983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (173, 1), (641, 1), (74660508983, 1)] : List FactorBlock).map factorBlockValue).prod) = 513318325004412779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_31
      · exact prime_oneHundredTwentySevenDU_173
      · exact prime_oneHundredTwentySevenDU_641
      · exact prime_oneHundredTwentySevenDU_74660508983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 513318325004412779) ^ 256659162502206389 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 513318325004412779) ^ 16558655645303638 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 513318325004412779) ^ 2967157948002386 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 513318325004412779) ^ 800808619351658 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 513318325004412779) ^ 6875366 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_574016912460446453 : Nat.Prime 574016912460446453 := by
  apply lucas_primality 574016912460446453 (2 : ZMod 574016912460446453)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (21114209, 1), (158059799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (21114209, 1), (158059799, 1)] : List FactorBlock).map factorBlockValue).prod) = 574016912460446453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_21114209
      · exact prime_oneHundredTwentySevenDU_158059799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 574016912460446453) ^ 287008456230223226 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 574016912460446453) ^ 13349230522335964 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 574016912460446453) ^ 27186285428 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 574016912460446453) ^ 3631643948 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_818657260566624041 : Nat.Prime 818657260566624041 := by
  apply lucas_primality 818657260566624041 (3 : ZMod 818657260566624041)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (197, 1), (103890515300333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (197, 1), (103890515300333, 1)] : List FactorBlock).map factorBlockValue).prod) = 818657260566624041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_197
      · exact prime_oneHundredTwentySevenDU_103890515300333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 818657260566624041) ^ 409328630283312020 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 818657260566624041) ^ 163731452113324808 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 818657260566624041) ^ 4155620612013320 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 818657260566624041) ^ 7880 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1334771425132142969 : Nat.Prime 1334771425132142969 := by
  apply lucas_primality 1334771425132142969 (3 : ZMod 1334771425132142969)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (7013, 1), (44111, 1), (31726141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (7013, 1), (44111, 1), (31726141, 1)] : List FactorBlock).map factorBlockValue).prod) = 1334771425132142969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_7013
      · exact prime_oneHundredTwentySevenDU_44111
      · exact prime_oneHundredTwentySevenDU_31726141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1334771425132142969) ^ 667385712566071484 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1334771425132142969) ^ 78515966184243704 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1334771425132142969) ^ 190328165568536 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1334771425132142969) ^ 30259378049288 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1334771425132142969) ^ 42071660248 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1922336260670414213 : Nat.Prime 1922336260670414213 := by
  apply lucas_primality 1922336260670414213 (2 : ZMod 1922336260670414213)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (67, 1), (27277, 1), (20228077459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (67, 1), (27277, 1), (20228077459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1922336260670414213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_67
      · exact prime_oneHundredTwentySevenDU_27277
      · exact prime_oneHundredTwentySevenDU_20228077459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1922336260670414213) ^ 961168130335207106 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1922336260670414213) ^ 147872020051570324 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1922336260670414213) ^ 28691585980155436 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1922336260670414213) ^ 70474621867156 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1922336260670414213) ^ 95033068 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_3201273910488331499 : Nat.Prime 3201273910488331499 := by
  apply lucas_primality 3201273910488331499 (2 : ZMod 3201273910488331499)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (367, 1), (5378719, 1), (810863813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (367, 1), (5378719, 1), (810863813, 1)] : List FactorBlock).map factorBlockValue).prod) = 3201273910488331499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_367
      · exact prime_oneHundredTwentySevenDU_5378719
      · exact prime_oneHundredTwentySevenDU_810863813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3201273910488331499) ^ 1600636955244165749 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3201273910488331499) ^ 8722817194791094 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3201273910488331499) ^ 595174038742 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3201273910488331499) ^ 3947979746 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_7866237642736879723 : Nat.Prime 7866237642736879723 := by
  apply lucas_primality 7866237642736879723 (2 : ZMod 7866237642736879723)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (3915511, 1), (14557926679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (3915511, 1), (14557926679, 1)] : List FactorBlock).map factorBlockValue).prod) = 7866237642736879723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_23
      · exact prime_oneHundredTwentySevenDU_3915511
      · exact prime_oneHundredTwentySevenDU_14557926679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7866237642736879723) ^ 3933118821368439861 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7866237642736879723) ^ 2622079214245626574 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7866237642736879723) ^ 342010332292907814 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7866237642736879723) ^ 2008993881702 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7866237642736879723) ^ 540340518 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_8378965959427830973 : Nat.Prime 8378965959427830973 := by
  apply lucas_primality 8378965959427830973 (5 : ZMod 8378965959427830973)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 2), (248574995829709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 2), (248574995829709, 1)] : List FactorBlock).map factorBlockValue).prod) = 8378965959427830973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_53
      · exact prime_oneHundredTwentySevenDU_248574995829709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8378965959427830973) ^ 4189482979713915486 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8378965959427830973) ^ 2792988653142610324 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8378965959427830973) ^ 158093697347694924 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8378965959427830973) ^ 33708 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_11155009133384380007 : Nat.Prime 11155009133384380007 := by
  apply lucas_primality 11155009133384380007 (5 : ZMod 11155009133384380007)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (353, 1), (15800296222924051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (353, 1), (15800296222924051, 1)] : List FactorBlock).map factorBlockValue).prod) = 11155009133384380007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_353
      · exact prime_oneHundredTwentySevenDU_15800296222924051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11155009133384380007) ^ 5577504566692190003 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 11155009133384380007) ^ 31600592445848102 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 11155009133384380007) ^ 706 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_11345355574437229277 : Nat.Prime 11345355574437229277 := by
  apply lucas_primality 11345355574437229277 (2 : ZMod 11345355574437229277)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (311, 1), (54611142222487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (311, 1), (54611142222487, 1)] : List FactorBlock).map factorBlockValue).prod) = 11345355574437229277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_167
      · exact prime_oneHundredTwentySevenDU_311
      · exact prime_oneHundredTwentySevenDU_54611142222487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11345355574437229277) ^ 5672677787218614638 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11345355574437229277) ^ 67936260924773828 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11345355574437229277) ^ 36480243004621316 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 11345355574437229277) ^ 207748 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_14308549047229986691 : Nat.Prime 14308549047229986691 := by
  apply lucas_primality 14308549047229986691 (2 : ZMod 14308549047229986691)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (97, 1), (73388465134277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (97, 1), (73388465134277, 1)] : List FactorBlock).map factorBlockValue).prod) = 14308549047229986691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_67
      · exact prime_oneHundredTwentySevenDU_97
      · exact prime_oneHundredTwentySevenDU_73388465134277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14308549047229986691) ^ 7154274523614993345 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14308549047229986691) ^ 4769516349076662230 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14308549047229986691) ^ 2861709809445997338 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14308549047229986691) ^ 213560433540746070 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14308549047229986691) ^ 147510814919896770 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 14308549047229986691) ^ 194970 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_17156406194461231067 : Nat.Prime 17156406194461231067 := by
  apply lucas_primality 17156406194461231067 (2 : ZMod 17156406194461231067)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (577, 1), (2017, 1), (7370799759437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (577, 1), (2017, 1), (7370799759437, 1)] : List FactorBlock).map factorBlockValue).prod) = 17156406194461231067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_577
      · exact prime_oneHundredTwentySevenDU_2017
      · exact prime_oneHundredTwentySevenDU_7370799759437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17156406194461231067) ^ 8578203097230615533 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17156406194461231067) ^ 29733806229568858 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17156406194461231067) ^ 8505902922390298 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17156406194461231067) ^ 2327618 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_17570511945202080269 : Nat.Prime 17570511945202080269 := by
  apply lucas_primality 17570511945202080269 (2 : ZMod 17570511945202080269)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (47, 1), (4918956311646719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (47, 1), (4918956311646719, 1)] : List FactorBlock).map factorBlockValue).prod) = 17570511945202080269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_47
      · exact prime_oneHundredTwentySevenDU_4918956311646719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17570511945202080269) ^ 8785255972601040134 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17570511945202080269) ^ 924763786589583172 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17570511945202080269) ^ 373840679685150644 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 17570511945202080269) ^ 3572 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_21862237518704203433 : Nat.Prime 21862237518704203433 := by
  apply lucas_primality 21862237518704203433 (3 : ZMod 21862237518704203433)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1973, 1), (12005219, 1), (16481981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1973, 1), (12005219, 1), (16481981, 1)] : List FactorBlock).map factorBlockValue).prod) = 21862237518704203433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_1973
      · exact prime_oneHundredTwentySevenDU_12005219
      · exact prime_oneHundredTwentySevenDU_16481981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21862237518704203433) ^ 10931118759352101716 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21862237518704203433) ^ 3123176788386314776 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21862237518704203433) ^ 11080708321694984 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21862237518704203433) ^ 1821061116728 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 21862237518704203433) ^ 1326432636872 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_28606773162452392307 : Nat.Prime 28606773162452392307 := by
  apply lucas_primality 28606773162452392307 (2 : ZMod 28606773162452392307)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (971, 1), (1772893, 1), (1186968193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (971, 1), (1772893, 1), (1186968193, 1)] : List FactorBlock).map factorBlockValue).prod) = 28606773162452392307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_971
      · exact prime_oneHundredTwentySevenDU_1772893
      · exact prime_oneHundredTwentySevenDU_1186968193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28606773162452392307) ^ 14303386581226196153 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 28606773162452392307) ^ 4086681880350341758 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 28606773162452392307) ^ 29461146408292886 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 28606773162452392307) ^ 16135645615642 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 28606773162452392307) ^ 24100707442 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_29458732215494761547 : Nat.Prime 29458732215494761547 := by
  apply lucas_primality 29458732215494761547 (2 : ZMod 29458732215494761547)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (857, 1), (9157, 1), (9826902647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (857, 1), (9157, 1), (9826902647, 1)] : List FactorBlock).map factorBlockValue).prod) = 29458732215494761547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_191
      · exact prime_oneHundredTwentySevenDU_857
      · exact prime_oneHundredTwentySevenDU_9157
      · exact prime_oneHundredTwentySevenDU_9826902647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29458732215494761547) ^ 14729366107747380773 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 29458732215494761547) ^ 154234200081124406 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 29458732215494761547) ^ 34374249959737178 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 29458732215494761547) ^ 3217072427158978 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 29458732215494761547) ^ 2997763718 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_49819518600249863999 : Nat.Prime 49819518600249863999 := by
  apply lucas_primality 49819518600249863999 (7 : ZMod 49819518600249863999)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (173, 1), (4436687, 1), (2496440873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (173, 1), (4436687, 1), (2496440873, 1)] : List FactorBlock).map factorBlockValue).prod) = 49819518600249863999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_173
      · exact prime_oneHundredTwentySevenDU_4436687
      · exact prime_oneHundredTwentySevenDU_2496440873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 49819518600249863999) ^ 24909759300124931999 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 49819518600249863999) ^ 3832270661557681846 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 49819518600249863999) ^ 287974095955201526 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 49819518600249863999) ^ 11228991046754 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 49819518600249863999) ^ 19956218126 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_90762844595497834217 : Nat.Prime 90762844595497834217 := by
  apply lucas_primality 90762844595497834217 (3 : ZMod 90762844595497834217)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11345355574437229277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11345355574437229277, 1)] : List FactorBlock).map factorBlockValue).prod) = 90762844595497834217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11345355574437229277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 90762844595497834217) ^ 45381422297748917108 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 90762844595497834217) ^ 8 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_104350758895652842229 : Nat.Prime 104350758895652842229 := by
  apply lucas_primality 104350758895652842229 (2 : ZMod 104350758895652842229)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (131, 1), (21092611, 1), (555373381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (131, 1), (21092611, 1), (555373381, 1)] : List FactorBlock).map factorBlockValue).prod) = 104350758895652842229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_131
      · exact prime_oneHundredTwentySevenDU_21092611
      · exact prime_oneHundredTwentySevenDU_555373381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104350758895652842229) ^ 52175379447826421114 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 104350758895652842229) ^ 6138279935038402484 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 104350758895652842229) ^ 796570678592769788 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 104350758895652842229) ^ 4947266077948 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 104350758895652842229) ^ 187892978788 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_120129428261892867211 : Nat.Prime 120129428261892867211 := by
  apply lucas_primality 120129428261892867211 (2 : ZMod 120129428261892867211)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1334771425132142969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1334771425132142969, 1)] : List FactorBlock).map factorBlockValue).prod) = 120129428261892867211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_1334771425132142969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 120129428261892867211) ^ 60064714130946433605 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 120129428261892867211) ^ 40043142753964289070 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 120129428261892867211) ^ 24025885652378573442 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 120129428261892867211) ^ 90 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_302758536703772744263 : Nat.Prime 302758536703772744263 := by
  apply lucas_primality 302758536703772744263 (3 : ZMod 302758536703772744263)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (43, 1), (4829146915235473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (43, 1), (4829146915235473, 1)] : List FactorBlock).map factorBlockValue).prod) = 302758536703772744263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_4829146915235473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 302758536703772744263) ^ 151379268351886372131 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 302758536703772744263) ^ 100919512234590914754 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 302758536703772744263) ^ 7040896202413319634 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 302758536703772744263) ^ 62694 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_334312418847101540023 : Nat.Prime 334312418847101540023 := by
  apply lucas_primality 334312418847101540023 (3 : ZMod 334312418847101540023)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11179951, 1), (1661269549229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11179951, 1), (1661269549229, 1)] : List FactorBlock).map factorBlockValue).prod) = 334312418847101540023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11179951
      · exact prime_oneHundredTwentySevenDU_1661269549229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 334312418847101540023) ^ 167156209423550770011 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 334312418847101540023) ^ 111437472949033846674 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 334312418847101540023) ^ 29902851886122 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 334312418847101540023) ^ 201239118 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_378779140954596227173 : Nat.Prime 378779140954596227173 := by
  apply lucas_primality 378779140954596227173 (2 : ZMod 378779140954596227173)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (21347, 1), (1478658753589873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (21347, 1), (1478658753589873, 1)] : List FactorBlock).map factorBlockValue).prod) = 378779140954596227173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_21347
      · exact prime_oneHundredTwentySevenDU_1478658753589873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 378779140954596227173) ^ 189389570477298113586 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 378779140954596227173) ^ 126259713651532075724 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 378779140954596227173) ^ 17743905043078476 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 378779140954596227173) ^ 256164 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_431408385340633584733 : Nat.Prime 431408385340633584733 := by
  apply lucas_primality 431408385340633584733 (2 : ZMod 431408385340633584733)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (149, 1), (241279857573061289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (149, 1), (241279857573061289, 1)] : List FactorBlock).map factorBlockValue).prod) = 431408385340633584733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_149
      · exact prime_oneHundredTwentySevenDU_241279857573061289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 431408385340633584733) ^ 215704192670316792366 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 431408385340633584733) ^ 143802795113544528244 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 431408385340633584733) ^ 2895358290876735468 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 431408385340633584733) ^ 1788 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_687685835647533346207 : Nat.Prime 687685835647533346207 := by
  apply lucas_primality 687685835647533346207 (3 : ZMod 687685835647533346207)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (7021997, 1), (1483834635403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (7021997, 1), (1483834635403, 1)] : List FactorBlock).map factorBlockValue).prod) = 687685835647533346207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_7021997
      · exact prime_oneHundredTwentySevenDU_1483834635403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 687685835647533346207) ^ 343842917823766673103 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 687685835647533346207) ^ 229228611882511115402 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 687685835647533346207) ^ 62516894149775758746 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 687685835647533346207) ^ 97933085936598 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 687685835647533346207) ^ 463451802 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1964367898115952425573 : Nat.Prime 1964367898115952425573 := by
  apply lucas_primality 1964367898115952425573 (2 : ZMod 1964367898115952425573)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (163, 1), (271, 1), (55339, 1), (28699649617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (163, 1), (271, 1), (55339, 1), (28699649617, 1)] : List FactorBlock).map factorBlockValue).prod) = 1964367898115952425573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_163
      · exact prime_oneHundredTwentySevenDU_271
      · exact prime_oneHundredTwentySevenDU_55339
      · exact prime_oneHundredTwentySevenDU_28699649617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1964367898115952425573) ^ 982183949057976212786 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1964367898115952425573) ^ 280623985445136060796 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1964367898115952425573) ^ 12051336798257376844 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1964367898115952425573) ^ 7248590029948163932 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1964367898115952425573) ^ 35496989430888748 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1964367898115952425573) ^ 68445710116 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_2030318087912754626201 : Nat.Prime 2030318087912754626201 := by
  apply lucas_primality 2030318087912754626201 (3 : ZMod 2030318087912754626201)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (739, 1), (5284649, 1), (2599402321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (739, 1), (5284649, 1), (2599402321, 1)] : List FactorBlock).map factorBlockValue).prod) = 2030318087912754626201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_739
      · exact prime_oneHundredTwentySevenDU_5284649
      · exact prime_oneHundredTwentySevenDU_2599402321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2030318087912754626201) ^ 1015159043956377313100 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2030318087912754626201) ^ 406063617582550925240 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2030318087912754626201) ^ 2747385775254065800 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2030318087912754626201) ^ 384191663043800 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 2030318087912754626201) ^ 781071122200 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_8064476232237745935409 : Nat.Prime 8064476232237745935409 := by
  apply lucas_primality 8064476232237745935409 (23 : ZMod 8064476232237745935409)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (2371526057, 1), (2623875739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (2371526057, 1), (2623875739, 1)] : List FactorBlock).map factorBlockValue).prod) = 8064476232237745935409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_2371526057
      · exact prime_oneHundredTwentySevenDU_2623875739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 8064476232237745935409) ^ 4032238116118872967704 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (23 : ZMod 8064476232237745935409) ^ 2688158744079248645136 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (23 : ZMod 8064476232237745935409) ^ 3400542957744 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (23 : ZMod 8064476232237745935409) ^ 3073497769872 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_22343815695840442575059 : Nat.Prime 22343815695840442575059 := by
  apply lucas_primality 22343815695840442575059 (2 : ZMod 22343815695840442575059)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (17, 1), (131, 1), (20983, 1), (4879142104181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (17, 1), (131, 1), (20983, 1), (4879142104181, 1)] : List FactorBlock).map factorBlockValue).prod) = 22343815695840442575059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_131
      · exact prime_oneHundredTwentySevenDU_20983
      · exact prime_oneHundredTwentySevenDU_4879142104181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22343815695840442575059) ^ 11171907847920221287529 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 22343815695840442575059) ^ 3191973670834348939294 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 22343815695840442575059) ^ 1314342099755320151474 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 22343815695840442575059) ^ 170563478594201851718 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 22343815695840442575059) ^ 1064853247669086526 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 22343815695840442575059) ^ 4579455818 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_36236088919048539734869 : Nat.Prime 36236088919048539734869 := by
  apply lucas_primality 36236088919048539734869 (2 : ZMod 36236088919048539734869)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (29, 1), (863887, 1), (5240555178091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (29, 1), (863887, 1), (5240555178091, 1)] : List FactorBlock).map factorBlockValue).prod) = 36236088919048539734869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_23
      · exact prime_oneHundredTwentySevenDU_29
      · exact prime_oneHundredTwentySevenDU_863887
      · exact prime_oneHundredTwentySevenDU_5240555178091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36236088919048539734869) ^ 18118044459524269867434 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36236088919048539734869) ^ 12078696306349513244956 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36236088919048539734869) ^ 1575482126915153901516 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36236088919048539734869) ^ 1249520307553397921892 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36236088919048539734869) ^ 41945403645440364 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 36236088919048539734869) ^ 6914551548 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_37713349477433197781209 : Nat.Prime 37713349477433197781209 := by
  apply lucas_primality 37713349477433197781209 (7 : ZMod 37713349477433197781209)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (659, 1), (907, 1), (59611, 1), (14700885673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (659, 1), (907, 1), (59611, 1), (14700885673, 1)] : List FactorBlock).map factorBlockValue).prod) = 37713349477433197781209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_659
      · exact prime_oneHundredTwentySevenDU_907
      · exact prime_oneHundredTwentySevenDU_59611
      · exact prime_oneHundredTwentySevenDU_14700885673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 37713349477433197781209) ^ 18856674738716598890604 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 37713349477433197781209) ^ 12571116492477732593736 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 37713349477433197781209) ^ 57228147917197568712 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 37713349477433197781209) ^ 41580319159242775944 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 37713349477433197781209) ^ 632657554435141128 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 37713349477433197781209) ^ 2565379414296 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_41939089086706183244671 : Nat.Prime 41939089086706183244671 := by
  apply lucas_primality 41939089086706183244671 (6 : ZMod 41939089086706183244671)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (73, 1), (414691, 1), (1783319, 1), (3699331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (73, 1), (414691, 1), (1783319, 1), (3699331, 1)] : List FactorBlock).map factorBlockValue).prod) = 41939089086706183244671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_73
      · exact prime_oneHundredTwentySevenDU_414691
      · exact prime_oneHundredTwentySevenDU_1783319
      · exact prime_oneHundredTwentySevenDU_3699331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 41939089086706183244671) ^ 20969544543353091622335 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 41939089086706183244671) ^ 13979696362235394414890 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 41939089086706183244671) ^ 8387817817341236648934 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 41939089086706183244671) ^ 5991298440958026177810 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 41939089086706183244671) ^ 574508069680906619790 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 41939089086706183244671) ^ 101133347689499370 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 41939089086706183244671) ^ 23517435235482930 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (6 : ZMod 41939089086706183244671) ^ 11336938783446570 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_183862594343171454786731 : Nat.Prime 183862594343171454786731 := by
  apply lucas_primality 183862594343171454786731 (2 : ZMod 183862594343171454786731)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (66919751, 1), (274750864424423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (66919751, 1), (274750864424423, 1)] : List FactorBlock).map factorBlockValue).prod) = 183862594343171454786731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_66919751
      · exact prime_oneHundredTwentySevenDU_274750864424423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 183862594343171454786731) ^ 91931297171585727393365 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 183862594343171454786731) ^ 36772518868634290957346 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 183862594343171454786731) ^ 2747508644244230 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 183862594343171454786731) ^ 669197510 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_369555700642291273278011 : Nat.Prime 369555700642291273278011 := by
  apply lucas_primality 369555700642291273278011 (2 : ZMod 369555700642291273278011)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (174443, 1), (45954367, 1), (4609985621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (174443, 1), (45954367, 1), (4609985621, 1)] : List FactorBlock).map factorBlockValue).prod) = 369555700642291273278011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_174443
      · exact prime_oneHundredTwentySevenDU_45954367
      · exact prime_oneHundredTwentySevenDU_4609985621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 369555700642291273278011) ^ 184777850321145636639005 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 369555700642291273278011) ^ 73911140128458254655602 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 369555700642291273278011) ^ 2118489710921569070 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 369555700642291273278011) ^ 8041797216841030 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 369555700642291273278011) ^ 80164176425810 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_411405798070101485065453 : Nat.Prime 411405798070101485065453 := by
  apply lucas_primality 411405798070101485065453 (5 : ZMod 411405798070101485065453)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (7838651, 1), (230194123331209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (7838651, 1), (230194123331209, 1)] : List FactorBlock).map factorBlockValue).prod) = 411405798070101485065453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_7838651
      · exact prime_oneHundredTwentySevenDU_230194123331209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 411405798070101485065453) ^ 205702899035050742532726 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 411405798070101485065453) ^ 137135266023367161688484 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 411405798070101485065453) ^ 21652936740531657108708 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 411405798070101485065453) ^ 52484260119515652 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 411405798070101485065453) ^ 1787212428 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_427890027389502079759771 : Nat.Prime 427890027389502079759771 := by
  apply lucas_primality 427890027389502079759771 (2 : ZMod 427890027389502079759771)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (8839, 1), (366941, 1), (209407504421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (8839, 1), (366941, 1), (209407504421, 1)] : List FactorBlock).map factorBlockValue).prod) = 427890027389502079759771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_8839
      · exact prime_oneHundredTwentySevenDU_366941
      · exact prime_oneHundredTwentySevenDU_209407504421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 427890027389502079759771) ^ 213945013694751039879885 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 427890027389502079759771) ^ 142630009129834026586590 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 427890027389502079759771) ^ 85578005477900415951954 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 427890027389502079759771) ^ 61127146769928868537110 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 427890027389502079759771) ^ 48409325420240081430 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 427890027389502079759771) ^ 1166100346893647970 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 427890027389502079759771) ^ 2043336644370 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_474084873215829094328719 : Nat.Prime 474084873215829094328719 := by
  apply lucas_primality 474084873215829094328719 (3 : ZMod 474084873215829094328719)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (8167, 1), (21589, 1), (64019418646633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (8167, 1), (21589, 1), (64019418646633, 1)] : List FactorBlock).map factorBlockValue).prod) = 474084873215829094328719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_8167
      · exact prime_oneHundredTwentySevenDU_21589
      · exact prime_oneHundredTwentySevenDU_64019418646633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 474084873215829094328719) ^ 237042436607914547164359 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 474084873215829094328719) ^ 158028291071943031442906 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 474084873215829094328719) ^ 67726410459404156332674 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 474084873215829094328719) ^ 58048839624810713154 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 474084873215829094328719) ^ 21959556867656171862 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 474084873215829094328719) ^ 7405329246 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1855464450718697613676663 : Nat.Prime 1855464450718697613676663 := by
  apply lucas_primality 1855464450718697613676663 (3 : ZMod 1855464450718697613676663)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (19, 1), (47, 1), (287576921, 1), (6439531807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (19, 1), (47, 1), (287576921, 1), (6439531807, 1)] : List FactorBlock).map factorBlockValue).prod) = 1855464450718697613676663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_47
      · exact prime_oneHundredTwentySevenDU_287576921
      · exact prime_oneHundredTwentySevenDU_6439531807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1855464450718697613676663) ^ 927732225359348806838331 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1855464450718697613676663) ^ 618488150239565871225554 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1855464450718697613676663) ^ 168678586428972510334242 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1855464450718697613676663) ^ 109144967689335153745686 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1855464450718697613676663) ^ 97656023722036716509298 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1855464450718697613676663) ^ 39477967036568034333546 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1855464450718697613676663) ^ 6452063135896422 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 1855464450718697613676663) ^ 288136545688266 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_3362925422886992660229863 : Nat.Prime 3362925422886992660229863 := by
  apply lucas_primality 3362925422886992660229863 (5 : ZMod 3362925422886992660229863)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1381, 1), (4129, 1), (169753, 1), (157920509293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1381, 1), (4129, 1), (169753, 1), (157920509293, 1)] : List FactorBlock).map factorBlockValue).prod) = 3362925422886992660229863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_1381
      · exact prime_oneHundredTwentySevenDU_4129
      · exact prime_oneHundredTwentySevenDU_169753
      · exact prime_oneHundredTwentySevenDU_157920509293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3362925422886992660229863) ^ 1681462711443496330114931 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3362925422886992660229863) ^ 305720492989726605475442 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3362925422886992660229863) ^ 2435137887680660869102 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3362925422886992660229863) ^ 814464863862192458278 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3362925422886992660229863) ^ 19810698031180554454 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 3362925422886992660229863) ^ 21295051782334 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_8940567719486629051681727 : Nat.Prime 8940567719486629051681727 := by
  apply lucas_primality 8940567719486629051681727 (5 : ZMod 8940567719486629051681727)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (197, 1), (751, 1), (9833, 1), (10607, 1), (22284709543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (197, 1), (751, 1), (9833, 1), (10607, 1), (22284709543, 1)] : List FactorBlock).map factorBlockValue).prod) = 8940567719486629051681727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_197
      · exact prime_oneHundredTwentySevenDU_751
      · exact prime_oneHundredTwentySevenDU_9833
      · exact prime_oneHundredTwentySevenDU_10607
      · exact prime_oneHundredTwentySevenDU_22284709543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8940567719486629051681727) ^ 4470283859743314525840863 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8940567719486629051681727) ^ 687735978422048388590902 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8940567719486629051681727) ^ 45383592484703700769958 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8940567719486629051681727) ^ 11904883780940917512226 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8940567719486629051681727) ^ 909241098290107703822 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8940567719486629051681727) ^ 842893157300521264418 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 8940567719486629051681727) ^ 401197408574482 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_12872761855371952014226931 : Nat.Prime 12872761855371952014226931 := by
  apply lucas_primality 12872761855371952014226931 (2 : ZMod 12872761855371952014226931)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (2647, 1), (28606773162452392307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (2647, 1), (28606773162452392307, 1)] : List FactorBlock).map factorBlockValue).prod) = 12872761855371952014226931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_2647
      · exact prime_oneHundredTwentySevenDU_28606773162452392307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12872761855371952014226931) ^ 6436380927685976007113465 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12872761855371952014226931) ^ 2574552371074390402845386 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12872761855371952014226931) ^ 757221285610114824366290 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12872761855371952014226931) ^ 4863151437616906692190 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 12872761855371952014226931) ^ 449990 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_15908867798374491236908553 : Nat.Prime 15908867798374491236908553 := by
  apply lucas_primality 15908867798374491236908553 (3 : ZMod 15908867798374491236908553)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (101, 1), (2503, 1), (7866237642736879723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (101, 1), (2503, 1), (7866237642736879723, 1)] : List FactorBlock).map factorBlockValue).prod) = 15908867798374491236908553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_101
      · exact prime_oneHundredTwentySevenDU_2503
      · exact prime_oneHundredTwentySevenDU_7866237642736879723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15908867798374491236908553) ^ 7954433899187245618454276 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15908867798374491236908553) ^ 157513542558163279573352 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15908867798374491236908553) ^ 6355920015331398816184 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 15908867798374491236908553) ^ 2022424 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_23343889036234211488486151 : Nat.Prime 23343889036234211488486151 := by
  apply lucas_primality 23343889036234211488486151 (7 : ZMod 23343889036234211488486151)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (14593, 1), (3335178349, 1), (9592671239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (14593, 1), (3335178349, 1), (9592671239, 1)] : List FactorBlock).map factorBlockValue).prod) = 23343889036234211488486151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_14593
      · exact prime_oneHundredTwentySevenDU_3335178349
      · exact prime_oneHundredTwentySevenDU_9592671239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23343889036234211488486151) ^ 11671944518117105744243075 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 23343889036234211488486151) ^ 4668777807246842297697230 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 23343889036234211488486151) ^ 1599663471269390220550 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 23343889036234211488486151) ^ 6999292569536350 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 23343889036234211488486151) ^ 2433512882347850 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_37480752441602208760345213 : Nat.Prime 37480752441602208760345213 := by
  apply lucas_primality 37480752441602208760345213 (5 : ZMod 37480752441602208760345213)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (137, 1), (878760479, 1), (218016322373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (137, 1), (878760479, 1), (218016322373, 1)] : List FactorBlock).map factorBlockValue).prod) = 37480752441602208760345213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_137
      · exact prime_oneHundredTwentySevenDU_878760479
      · exact prime_oneHundredTwentySevenDU_218016322373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 37480752441602208760345213) ^ 18740376220801104380172606 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 37480752441602208760345213) ^ 12493584147200736253448404 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 37480752441602208760345213) ^ 5354393205943172680049316 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 37480752441602208760345213) ^ 2204750143623659338843836 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 37480752441602208760345213) ^ 273582134610235100440476 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 37480752441602208760345213) ^ 42651841243764228 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 37480752441602208760345213) ^ 171917185069644 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_78900627578065395845477101 : Nat.Prime 78900627578065395845477101 := by
  apply lucas_primality 78900627578065395845477101 (2 : ZMod 78900627578065395845477101)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (20407, 1), (38438693, 1), (335282916907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (20407, 1), (38438693, 1), (335282916907, 1)] : List FactorBlock).map factorBlockValue).prod) = 78900627578065395845477101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_20407
      · exact prime_oneHundredTwentySevenDU_38438693
      · exact prime_oneHundredTwentySevenDU_335282916907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78900627578065395845477101) ^ 39450313789032697922738550 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78900627578065395845477101) ^ 26300209192688465281825700 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78900627578065395845477101) ^ 15780125515613079169095420 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78900627578065395845477101) ^ 3866351133339804765300 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78900627578065395845477101) ^ 2052635545596344700 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 78900627578065395845477101) ^ 235325522415300 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_119164995461157498645986447 : Nat.Prime 119164995461157498645986447 := by
  apply lucas_primality 119164995461157498645986447 (5 : ZMod 119164995461157498645986447)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (59, 1), (3220956047, 1), (28502910546241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (59, 1), (3220956047, 1), (28502910546241, 1)] : List FactorBlock).map factorBlockValue).prod) = 119164995461157498645986447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_59
      · exact prime_oneHundredTwentySevenDU_3220956047
      · exact prime_oneHundredTwentySevenDU_28502910546241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 119164995461157498645986447) ^ 59582497730578749322993223 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 119164995461157498645986447) ^ 10833181405559772604180586 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 119164995461157498645986447) ^ 2019745685782330485525194 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 119164995461157498645986447) ^ 36996777889020818 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (5 : ZMod 119164995461157498645986447) ^ 4180800949006 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_131133532123195151348421767 : Nat.Prime 131133532123195151348421767 := by
  apply lucas_primality 131133532123195151348421767 (7 : ZMod 131133532123195151348421767)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (41, 1), (89, 1), (1944504959, 1), (64619680691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (41, 1), (89, 1), (1944504959, 1), (64619680691, 1)] : List FactorBlock).map factorBlockValue).prod) = 131133532123195151348421767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_11
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_41
      · exact prime_oneHundredTwentySevenDU_89
      · exact prime_oneHundredTwentySevenDU_1944504959
      · exact prime_oneHundredTwentySevenDU_64619680691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 131133532123195151348421767) ^ 65566766061597575674210883 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 131133532123195151348421767) ^ 11921230193017741031674706 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 131133532123195151348421767) ^ 10087194778707319334493982 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 131133532123195151348421767) ^ 3198378832273052471912726 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 131133532123195151348421767) ^ 1473410473294327543240694 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 131133532123195151348421767) ^ 67438003444657274 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 131133532123195151348421767) ^ 2029312598281826 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_623020308220159536489389723 : Nat.Prime 623020308220159536489389723 := by
  apply lucas_primality 623020308220159536489389723 (2 : ZMod 623020308220159536489389723)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (41351, 1), (90762844595497834217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (41351, 1), (90762844595497834217, 1)] : List FactorBlock).map factorBlockValue).prod) = 623020308220159536489389723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_83
      · exact prime_oneHundredTwentySevenDU_41351
      · exact prime_oneHundredTwentySevenDU_90762844595497834217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 623020308220159536489389723) ^ 311510154110079768244694861 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 623020308220159536489389723) ^ 7506268773736861885414334 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 623020308220159536489389723) ^ 15066632202852640480022 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 623020308220159536489389723) ^ 6864266 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_652816931656775862147577927 : Nat.Prime 652816931656775862147577927 := by
  apply lucas_primality 652816931656775862147577927 (3 : ZMod 652816931656775862147577927)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1973, 1), (11884359667, 1), (356938944587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1973, 1), (11884359667, 1), (356938944587, 1)] : List FactorBlock).map factorBlockValue).prod) = 652816931656775862147577927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_1973
      · exact prime_oneHundredTwentySevenDU_11884359667
      · exact prime_oneHundredTwentySevenDU_356938944587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 652816931656775862147577927) ^ 326408465828387931073788963 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 652816931656775862147577927) ^ 217605643885591954049192642 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 652816931656775862147577927) ^ 50216687050521220165198302 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 652816931656775862147577927) ^ 330875282137240680257262 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 652816931656775862147577927) ^ 54930761938271778 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 652816931656775862147577927) ^ 1828931646593298 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1007703988463479518751294787 : Nat.Prime 1007703988463479518751294787 := by
  apply lucas_primality 1007703988463479518751294787 (2 : ZMod 1007703988463479518751294787)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (421, 1), (45197, 1), (81980158691670443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (421, 1), (45197, 1), (81980158691670443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1007703988463479518751294787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_17
      · exact prime_oneHundredTwentySevenDU_19
      · exact prime_oneHundredTwentySevenDU_421
      · exact prime_oneHundredTwentySevenDU_45197
      · exact prime_oneHundredTwentySevenDU_81980158691670443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1007703988463479518751294787) ^ 503851994231739759375647393 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007703988463479518751294787) ^ 59276705203734089338311458 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007703988463479518751294787) ^ 53037052024393658881647094 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007703988463479518751294787) ^ 2393596172122279141927066 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007703988463479518751294787) ^ 22295815838738843700938 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007703988463479518751294787) ^ 12292047302 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_1080200678280996030891675707 : Nat.Prime 1080200678280996030891675707 := by
  apply lucas_primality 1080200678280996030891675707 (2 : ZMod 1080200678280996030891675707)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (15787, 1), (302758536703772744263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (15787, 1), (302758536703772744263, 1)] : List FactorBlock).map factorBlockValue).prod) = 1080200678280996030891675707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_113
      · exact prime_oneHundredTwentySevenDU_15787
      · exact prime_oneHundredTwentySevenDU_302758536703772744263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1080200678280996030891675707) ^ 540100339140498015445837853 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1080200678280996030891675707) ^ 9559298037884920627359962 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1080200678280996030891675707) ^ 68423429295052640203438 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 1080200678280996030891675707) ^ 3567862 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_3412452142751328370316884619 : Nat.Prime 3412452142751328370316884619 := by
  apply lucas_primality 3412452142751328370316884619 (2 : ZMod 3412452142751328370316884619)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2470424681537, 1), (98665862370451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2470424681537, 1), (98665862370451, 1)] : List FactorBlock).map factorBlockValue).prod) = 3412452142751328370316884619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_2470424681537
      · exact prime_oneHundredTwentySevenDU_98665862370451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3412452142751328370316884619) ^ 1706226071375664185158442309 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3412452142751328370316884619) ^ 487493163250189767188126374 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3412452142751328370316884619) ^ 1381322073186314 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 3412452142751328370316884619) ^ 34585945541518 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_7507394714052922414697146163 : Nat.Prime 7507394714052922414697146163 := by
  apply lucas_primality 7507394714052922414697146163 (2 : ZMod 7507394714052922414697146163)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (401, 1), (10331, 1), (102752333, 1), (678324458419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (401, 1), (10331, 1), (102752333, 1), (678324458419, 1)] : List FactorBlock).map factorBlockValue).prod) = 7507394714052922414697146163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_401
      · exact prime_oneHundredTwentySevenDU_10331
      · exact prime_oneHundredTwentySevenDU_102752333
      · exact prime_oneHundredTwentySevenDU_678324458419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7507394714052922414697146163) ^ 3753697357026461207348573081 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7507394714052922414697146163) ^ 577491901080994031899780474 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7507394714052922414697146163) ^ 18721682578685592056601362 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7507394714052922414697146163) ^ 726686159525014269160502 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7507394714052922414697146163) ^ 73063009810715659514 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 7507394714052922414697146163) ^ 11067557156276998 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_8341549682281024905219051289 : Nat.Prime 8341549682281024905219051289 := by
  apply lucas_primality 8341549682281024905219051289 (7 : ZMod 8341549682281024905219051289)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (12872761855371952014226931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (12872761855371952014226931, 1)] : List FactorBlock).map factorBlockValue).prod) = 8341549682281024905219051289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_12872761855371952014226931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 8341549682281024905219051289) ^ 4170774841140512452609525644 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 8341549682281024905219051289) ^ 2780516560760341635073017096 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (7 : ZMod 8341549682281024905219051289) ^ 648 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_10724849591504174878138780231 : Nat.Prime 10724849591504174878138780231 := by
  apply lucas_primality 10724849591504174878138780231 (3 : ZMod 10724849591504174878138780231)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (119164995461157498645986447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (119164995461157498645986447, 1)] : List FactorBlock).map factorBlockValue).prod) = 10724849591504174878138780231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_5
      · exact prime_oneHundredTwentySevenDU_119164995461157498645986447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10724849591504174878138780231) ^ 5362424795752087439069390115 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10724849591504174878138780231) ^ 3574949863834724959379593410 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10724849591504174878138780231) ^ 2144969918300834975627756046 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 10724849591504174878138780231) ^ 90 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_50049298093686149431314307763 : Nat.Prime 50049298093686149431314307763 := by
  apply lucas_primality 50049298093686149431314307763 (2 : ZMod 50049298093686149431314307763)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13487, 1), (1855464450718697613676663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13487, 1), (1855464450718697613676663, 1)] : List FactorBlock).map factorBlockValue).prod) = 50049298093686149431314307763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_13487
      · exact prime_oneHundredTwentySevenDU_1855464450718697613676663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50049298093686149431314307763) ^ 25024649046843074715657153881 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 50049298093686149431314307763) ^ 3710928901437395227353326 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 50049298093686149431314307763) ^ 26974 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_75073947140529224146971461627 : Nat.Prime 75073947140529224146971461627 := by
  apply lucas_primality 75073947140529224146971461627 (2 : ZMod 75073947140529224146971461627)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8402917, 1), (11292781, 1), (395574488127869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8402917, 1), (11292781, 1), (395574488127869, 1)] : List FactorBlock).map factorBlockValue).prod) = 75073947140529224146971461627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_8402917
      · exact prime_oneHundredTwentySevenDU_11292781
      · exact prime_oneHundredTwentySevenDU_395574488127869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75073947140529224146971461627) ^ 37536973570264612073485730813 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 75073947140529224146971461627) ^ 8934272127230249227378 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 75073947140529224146971461627) ^ 6647959182111937187746 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 75073947140529224146971461627) ^ 189784602884354 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_75073947140529224146971461647 : Nat.Prime 75073947140529224146971461647 := by
  apply lucas_primality 75073947140529224146971461647 (3 : ZMod 75073947140529224146971461647)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (52673, 1), (2030318087912754626201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (52673, 1), (2030318087912754626201, 1)] : List FactorBlock).map factorBlockValue).prod) = 75073947140529224146971461647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_3
      · exact prime_oneHundredTwentySevenDU_13
      · exact prime_oneHundredTwentySevenDU_52673
      · exact prime_oneHundredTwentySevenDU_2030318087912754626201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75073947140529224146971461647) ^ 37536973570264612073485730823 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 75073947140529224146971461647) ^ 25024649046843074715657153882 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 75073947140529224146971461647) ^ 5774919010809940318997804742 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 75073947140529224146971461647) ^ 1425283297714753747593102 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 75073947140529224146971461647) ^ 36976446 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_150147894281058448293942923219 : Nat.Prime 150147894281058448293942923219 := by
  apply lucas_primality 150147894281058448293942923219 (2 : ZMod 150147894281058448293942923219)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (103, 1), (839, 1), (4451, 1), (8498551, 1), (560149211197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (103, 1), (839, 1), (4451, 1), (8498551, 1), (560149211197, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_41
      · exact prime_oneHundredTwentySevenDU_103
      · exact prime_oneHundredTwentySevenDU_839
      · exact prime_oneHundredTwentySevenDU_4451
      · exact prime_oneHundredTwentySevenDU_8498551
      · exact prime_oneHundredTwentySevenDU_560149211197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 150147894281058448293942923219) ^ 75073947140529224146971461609 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 150147894281058448293942923219) ^ 3662143762952645080340071298 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 150147894281058448293942923219) ^ 1457746546418043187319834206 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 150147894281058448293942923219) ^ 178960541455373597489800862 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 150147894281058448293942923219) ^ 33733519272311491416298118 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 150147894281058448293942923219) ^ 17667469934705157184318 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (2 : ZMod 150147894281058448293942923219) ^ 268049818297883194 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySevenDU_150147894281058448293942923249 : Nat.Prime 150147894281058448293942923249 := by
  apply lucas_primality 150147894281058448293942923249 (3 : ZMod 150147894281058448293942923249)
  · rw [← oneHundredTwentySevenDUFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (43, 1), (53, 1), (2467, 1), (258351671, 1), (131849483749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (43, 1), (53, 1), (2467, 1), (258351671, 1), (131849483749, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySevenDU_2
      · exact prime_oneHundredTwentySevenDU_7
      · exact prime_oneHundredTwentySevenDU_43
      · exact prime_oneHundredTwentySevenDU_53
      · exact prime_oneHundredTwentySevenDU_2467
      · exact prime_oneHundredTwentySevenDU_258351671
      · exact prime_oneHundredTwentySevenDU_131849483749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 150147894281058448293942923249) ^ 75073947140529224146971461624 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 150147894281058448293942923249) ^ 21449699183008349756277560464 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 150147894281058448293942923249) ^ 3491811494908336006835881936 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 150147894281058448293942923249) ^ 2832979137378461288564960816 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 150147894281058448293942923249) ^ 60862543283769131858104144 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 150147894281058448293942923249) ^ 581176400755923302288 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide
    · change (3 : ZMod 150147894281058448293942923249) ^ 1138782572458856752 ≠ 1
      rw [← oneHundredTwentySevenDUFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923200 : Nat.totient 150147894281058448293942923200 = 59585903223086361478339584000 := by
  rw [← show ((([(2, 6), (5, 2), (127, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_127, prime_oneHundredTwentySevenDU_171401, prime_oneHundredTwentySevenDU_714027719, prime_oneHundredTwentySevenDU_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923201 : Nat.totient 150147894281058448293942923201 = 138598034844769449470144245440 := by
  rw [← show ((([(13, 2), (6500941, 1), (1482745087, 1), (92170049987, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_13, prime_oneHundredTwentySevenDU_6500941, prime_oneHundredTwentySevenDU_1482745087, prime_oneHundredTwentySevenDU_92170049987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923202 : Nat.totient 150147894281058448293942923202 = 50049298093686149431314307728 := by
  rw [← show ((([(2, 1), (3, 2), (8341549682281024905219051289, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_8341549682281024905219051289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923203 : Nat.totient 150147894281058448293942923203 = 135709079434272480854220612000 := by
  rw [← show ((([(11, 1), (173, 1), (78900627578065395845477101, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_11, prime_oneHundredTwentySevenDU_173, prime_oneHundredTwentySevenDU_78900627578065395845477101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923204 : Nat.totient 150147894281058448293942923204 = 73476629115605538670193106240 := by
  rw [← show ((([(2, 2), (47, 1), (111820243111, 1), (7142347305938953, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_47, prime_oneHundredTwentySevenDU_111820243111, prime_oneHundredTwentySevenDU_7142347305938953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923205 : Nat.totient 150147894281058448293942923205 = 77950201812628688665351004160 := by
  rw [← show ((([(3, 1), (5, 1), (43, 1), (353, 1), (1741, 1), (378779140954596227173, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_43, prime_oneHundredTwentySevenDU_353, prime_oneHundredTwentySevenDU_1741, prime_oneHundredTwentySevenDU_378779140954596227173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923206 : Nat.totient 150147894281058448293942923206 = 63467602960715600015827250496 := by
  rw [← show ((([(2, 1), (7, 1), (73, 1), (626305439, 1), (234575238662144707, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_73, prime_oneHundredTwentySevenDU_626305439, prime_oneHundredTwentySevenDU_234575238662144707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923207 : Nat.totient 150147894281058448293942923207 = 150103677896197163320698472320 := by
  rw [← show ((([(3547, 1), (79633, 1), (323626187, 1), (1642560307711, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3547, prime_oneHundredTwentySevenDU_79633, prime_oneHundredTwentySevenDU_323626187, prime_oneHundredTwentySevenDU_1642560307711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923208 : Nat.totient 150147894281058448293942923208 = 48358042268145564839688115200 := by
  rw [← show ((([(2, 3), (3, 1), (31, 1), (631, 1), (13676753, 1), (23384815479528299, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_31, prime_oneHundredTwentySevenDU_631, prime_oneHundredTwentySevenDU_13676753, prime_oneHundredTwentySevenDU_23384815479528299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923209 : Nat.totient 150147894281058448293942923209 = 139779184018955050171879215120 := by
  rw [← show ((([(19, 1), (79, 1), (211, 1), (474084873215829094328719, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_19, prime_oneHundredTwentySevenDU_79, prime_oneHundredTwentySevenDU_211, prime_oneHundredTwentySevenDU_474084873215829094328719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923210 : Nat.totient 150147894281058448293942923210 = 57447889985796275868986857488 := by
  rw [← show ((([(2, 1), (5, 1), (23, 1), (652816931656775862147577927, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_23, prime_oneHundredTwentySevenDU_652816931656775862147577927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923211 : Nat.totient 150147894281058448293942923211 = 100028547611889248038968981504 := by
  rw [← show ((([(3, 3), (1429, 1), (174706253, 1), (22274850793972289, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_1429, prime_oneHundredTwentySevenDU_174706253, prime_oneHundredTwentySevenDU_22274850793972289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923212 : Nat.totient 150147894281058448293942923212 = 75073945754695541387316844800 := by
  rw [← show ((([(2, 2), (55075381, 1), (3358851191, 1), (202913518193, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_55075381, prime_oneHundredTwentySevenDU_3358851191, prime_oneHundredTwentySevenDU_202913518193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923213 : Nat.totient 150147894281058448293942923213 = 128695627757885761525186503360 := by
  rw [← show ((([(7, 1), (50129, 1), (427890027389502079759771, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_50129, prime_oneHundredTwentySevenDU_427890027389502079759771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923214 : Nat.totient 150147894281058448293942923214 = 41999410987708656865438577280 := by
  rw [← show ((([(2, 1), (3, 1), (11, 2), (13, 1), (15908867798374491236908553, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_11, prime_oneHundredTwentySevenDU_13, prime_oneHundredTwentySevenDU_15908867798374491236908553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923215 : Nat.totient 150147894281058448293942923215 = 119593781296353978029760650592 := by
  rw [← show ((([(5, 1), (229, 1), (131133532123195151348421767, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_229, prime_oneHundredTwentySevenDU_131133532123195151348421767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923216 : Nat.totient 150147894281058448293942923216 = 70647224768788059962607575040 := by
  rw [← show ((([(2, 4), (17, 1), (6961, 1), (154487, 1), (513318325004412779, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_17, prime_oneHundredTwentySevenDU_6961, prime_oneHundredTwentySevenDU_154487, prime_oneHundredTwentySevenDU_513318325004412779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923217 : Nat.totient 150147894281058448293942923217 = 95524546937250673175286382848 := by
  rw [← show ((([(3, 1), (29, 1), (107, 1), (619, 1), (1483, 1), (17570511945202080269, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_29, prime_oneHundredTwentySevenDU_107, prime_oneHundredTwentySevenDU_619, prime_oneHundredTwentySevenDU_1483, prime_oneHundredTwentySevenDU_17570511945202080269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923218 : Nat.totient 150147894281058448293942923218 = 72429044395037150390702400000 := by
  rw [← show ((([(2, 1), (41, 1), (103, 1), (839, 1), (4451, 1), (8498551, 1), (560149211197, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_41, prime_oneHundredTwentySevenDU_103, prime_oneHundredTwentySevenDU_839, prime_oneHundredTwentySevenDU_4451, prime_oneHundredTwentySevenDU_8498551, prime_oneHundredTwentySevenDU_560149211197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923219 : Nat.totient 150147894281058448293942923219 = 150147894281058448293942923218 := by
  rw [← show ((([(150147894281058448293942923219, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_150147894281058448293942923219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923220 : Nat.totient 150147894281058448293942923220 = 34319518692813359610044096448 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (7, 1), (119164995461157498645986447, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_119164995461157498645986447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923221 : Nat.totient 150147894281058448293942923221 = 150147894281054661509053108000 := by
  rw [← show ((([(40074594091901, 1), (3746710295723321, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_40074594091901, prime_oneHundredTwentySevenDU_3746710295723321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923222 : Nat.totient 150147894281058448293942923222 = 74832670597688176699001548800 := by
  rw [← show ((([(2, 1), (313, 1), (52571, 1), (393138017, 1), (11605226786521, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_313, prime_oneHundredTwentySevenDU_52571, prime_oneHundredTwentySevenDU_393138017, prime_oneHundredTwentySevenDU_11605226786521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923223 : Nat.totient 150147894281058448293942923223 = 100097857075971014280081788600 := by
  rw [← show ((([(3, 1), (135431, 1), (369555700642291273278011, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_135431, prime_oneHundredTwentySevenDU_369555700642291273278011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923224 : Nat.totient 150147894281058448293942923224 = 75060495438837676176330519840 := by
  rw [← show ((([(2, 3), (5581, 1), (3362925422886992660229863, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_5581, prime_oneHundredTwentySevenDU_3362925422886992660229863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923225 : Nat.totient 150147894281058448293942923225 = 109187310388756678239965760000 := by
  rw [← show ((([(5, 2), (11, 1), (9791, 1), (20853541, 1), (2674112605937369, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_11, prime_oneHundredTwentySevenDU_9791, prime_oneHundredTwentySevenDU_20853541, prime_oneHundredTwentySevenDU_2674112605937369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923226 : Nat.totient 150147894281058448293942923226 = 50049297853427292907111945200 := by
  rw [← show ((([(2, 1), (3, 1), (208314061, 1), (120129428261892867211, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_208314061, prime_oneHundredTwentySevenDU_120129428261892867211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923227 : Nat.totient 150147894281058448293942923227 = 117463517387822717356075776000 := by
  rw [← show ((([(7, 1), (13, 1), (89, 1), (34434971, 1), (372185651, 1), (1446533513, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_13, prime_oneHundredTwentySevenDU_89, prime_oneHundredTwentySevenDU_34434971, prime_oneHundredTwentySevenDU_372185651, prime_oneHundredTwentySevenDU_1446533513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923228 : Nat.totient 150147894281058448293942923228 = 71122686764159536600579104240 := by
  rw [← show ((([(2, 2), (19, 1), (128762562143, 1), (15343203451594771, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_19, prime_oneHundredTwentySevenDU_128762562143, prime_oneHundredTwentySevenDU_15343203451594771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923229 : Nat.totient 150147894281058448293942923229 = 100098596010619905566262120072 := by
  rw [← show ((([(3, 2), (566321023, 1), (29458732215494761547, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_566321023, prime_oneHundredTwentySevenDU_29458732215494761547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923230 : Nat.totient 150147894281058448293942923230 = 58435937233322697294170411520 := by
  rw [← show ((([(2, 1), (5, 1), (37, 1), (151186778161, 1), (2684131010758039, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_37, prime_oneHundredTwentySevenDU_151186778161, prime_oneHundredTwentySevenDU_2684131010758039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923231 : Nat.totient 150147894281058448293942923231 = 150139639891703973791566558080 := by
  rw [← show ((([(18223, 1), (10064617, 1), (818657260566624041, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_18223, prime_oneHundredTwentySevenDU_10064617, prime_oneHundredTwentySevenDU_818657260566624041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923232 : Nat.totient 150147894281058448293942923232 = 49302293644526654663682748800 := by
  rw [← show ((([(2, 5), (3, 1), (67, 1), (23343889036234211488486151, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_67, prime_oneHundredTwentySevenDU_23343889036234211488486151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923233 : Nat.totient 150147894281058448293942923233 = 134689069478535585855620308992 := by
  rw [← show ((([(17, 1), (23, 1), (337, 1), (1657, 1), (687685835647533346207, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_17, prime_oneHundredTwentySevenDU_23, prime_oneHundredTwentySevenDU_337, prime_oneHundredTwentySevenDU_1657, prime_oneHundredTwentySevenDU_687685835647533346207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923234 : Nat.totient 150147894281058448293942923234 = 64349097549025049268832681380 := by
  rw [← show ((([(2, 1), (7, 1), (10724849591504174878138780231, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_10724849591504174878138780231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923235 : Nat.totient 150147894281058448293942923235 = 79803365933434812747788113920 := by
  rw [← show ((([(3, 1), (5, 1), (307, 1), (5477, 1), (869203, 1), (35842421, 1), (191085757, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_307, prime_oneHundredTwentySevenDU_5477, prime_oneHundredTwentySevenDU_869203, prime_oneHundredTwentySevenDU_35842421, prime_oneHundredTwentySevenDU_191085757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923236 : Nat.totient 150147894281058448293942923236 = 68249042855026567406337692360 := by
  rw [← show ((([(2, 2), (11, 1), (3412452142751328370316884619, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_11, prime_oneHundredTwentySevenDU_3412452142751328370316884619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923237 : Nat.totient 150147894281058448293942923237 = 149862592792261666152724103424 := by
  rw [← show ((([(569, 1), (6997, 1), (37713349477433197781209, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_569, prime_oneHundredTwentySevenDU_6997, prime_oneHundredTwentySevenDU_37713349477433197781209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923238 : Nat.totient 150147894281058448293942923238 = 49888367874735390108384031080 := by
  rw [← show ((([(2, 1), (3, 3), (311, 1), (8940567719486629051681727, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_311, prime_oneHundredTwentySevenDU_8940567719486629051681727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923239 : Nat.totient 150147894281058448293942923239 = 142181843813027073238620211200 := by
  rw [← show ((([(31, 1), (61, 1), (193, 1), (411405798070101485065453, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_31, prime_oneHundredTwentySevenDU_61, prime_oneHundredTwentySevenDU_193, prime_oneHundredTwentySevenDU_411405798070101485065453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923240 : Nat.totient 150147894281058448293942923240 = 55295616624848168671954944000 := by
  rw [← show ((([(2, 3), (5, 1), (13, 1), (401, 1), (10331, 1), (102752333, 1), (678324458419, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_13, prime_oneHundredTwentySevenDU_401, prime_oneHundredTwentySevenDU_10331, prime_oneHundredTwentySevenDU_102752333, prime_oneHundredTwentySevenDU_678324458419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923241 : Nat.totient 150147894281058448293942923241 = 85798796731747411315051398528 := by
  rw [← show ((([(3, 1), (7, 1), (300012461389, 1), (23832009159108889, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_300012461389, prime_oneHundredTwentySevenDU_23832009159108889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923242 : Nat.totient 150147894281058448293942923242 = 74628008190709758884376668160 := by
  rw [← show ((([(2, 1), (179, 1), (4409, 1), (8209, 1), (147211, 1), (78716468506589, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_179, prime_oneHundredTwentySevenDU_4409, prime_oneHundredTwentySevenDU_8209, prime_oneHundredTwentySevenDU_147211, prime_oneHundredTwentySevenDU_78716468506589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923243 : Nat.totient 150147894281058448293942923243 = 149524873972838288757453533280 := by
  rw [← show ((([(241, 1), (623020308220159536489389723, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_241, prime_oneHundredTwentySevenDU_623020308220159536489389723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923244 : Nat.totient 150147894281058448293942923244 = 50043572898373701247047045760 := by
  rw [← show ((([(2, 2), (3, 1), (10391, 1), (55079, 1), (21862237518704203433, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_10391, prime_oneHundredTwentySevenDU_55079, prime_oneHundredTwentySevenDU_21862237518704203433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923245 : Nat.totient 150147894281058448293942923245 = 119238235624526858707324793856 := by
  rw [← show ((([(5, 1), (137, 1), (36467, 1), (3514499, 1), (1710272108793769, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_137, prime_oneHundredTwentySevenDU_36467, prime_oneHundredTwentySevenDU_3514499, prime_oneHundredTwentySevenDU_1710272108793769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923246 : Nat.totient 150147894281058448293942923246 = 72485190340570560559131336288 := by
  rw [← show ((([(2, 1), (29, 1), (36073429069, 1), (71763535232472623, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_29, prime_oneHundredTwentySevenDU_36073429069, prime_oneHundredTwentySevenDU_71763535232472623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923247 : Nat.totient 150147894281058448293942923247 = 85405964548070289617601085440 := by
  rw [← show ((([(3, 2), (11, 1), (19, 1), (113, 1), (2113, 1), (334312418847101540023, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_11, prime_oneHundredTwentySevenDU_19, prime_oneHundredTwentySevenDU_113, prime_oneHundredTwentySevenDU_2113, prime_oneHundredTwentySevenDU_334312418847101540023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923248 : Nat.totient 150147894281058448293942923248 = 61641711786630549913589053440 := by
  rw [← show ((([(2, 4), (7, 2), (43, 1), (53, 1), (2467, 1), (258351671, 1), (131849483749, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_43, prime_oneHundredTwentySevenDU_53, prime_oneHundredTwentySevenDU_2467, prime_oneHundredTwentySevenDU_258351671, prime_oneHundredTwentySevenDU_131849483749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923249 : Nat.totient 150147894281058448293942923249 = 150147894281058448293942923248 := by
  rw [← show ((([(150147894281058448293942923249, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_150147894281058448293942923249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923250 : Nat.totient 150147894281058448293942923250 = 37684051605705208226152448000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 3), (17, 1), (299681, 1), (1115711969, 1), (35220681887, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_17, prime_oneHundredTwentySevenDU_299681, prime_oneHundredTwentySevenDU_1115711969, prime_oneHundredTwentySevenDU_35220681887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923251 : Nat.totient 150147894281058448293942923251 = 145182672335036723221213926304 := by
  rw [← show ((([(47, 1), (83, 1), (2243453, 1), (17156406194461231067, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_47, prime_oneHundredTwentySevenDU_83, prime_oneHundredTwentySevenDU_2243453, prime_oneHundredTwentySevenDU_17156406194461231067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923252 : Nat.totient 150147894281058448293942923252 = 75073931558298516169197809280 := by
  rw [← show ((([(2, 2), (8402917, 1), (11292781, 1), (395574488127869, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_8402917, prime_oneHundredTwentySevenDU_11292781, prime_oneHundredTwentySevenDU_395574488127869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923253 : Nat.totient 150147894281058448293942923253 = 92397400115926507186823409600 := by
  rw [← show ((([(3, 1), (13, 1), (72211, 1), (3772627, 1), (14132123075388491, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_13, prime_oneHundredTwentySevenDU_72211, prime_oneHundredTwentySevenDU_3772627, prime_oneHundredTwentySevenDU_14132123075388491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923254 : Nat.totient 150147894281058448293942923254 = 75073947140529224146971461626 := by
  rw [← show ((([(2, 1), (75073947140529224146971461627, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_75073947140529224146971461627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923255 : Nat.totient 150147894281058448293942923255 = 102958556077307160675541485312 := by
  rw [← show ((([(5, 1), (7, 1), (90879251849, 1), (47204832228698357, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_90879251849, prime_oneHundredTwentySevenDU_47204832228698357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923256 : Nat.totient 150147894281058448293942923256 = 47553194308396782282109747200 := by
  rw [← show ((([(2, 3), (3, 2), (23, 1), (181, 1), (857, 1), (31706933, 1), (18435090831041, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_23, prime_oneHundredTwentySevenDU_181, prime_oneHundredTwentySevenDU_857, prime_oneHundredTwentySevenDU_31706933, prime_oneHundredTwentySevenDU_18435090831041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923257 : Nat.totient 150147894281058448293942923257 = 150129624651949218773953769472 := by
  rw [← show ((([(9929, 1), (47743, 1), (52318543, 1), (6054083257217, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_9929, prime_oneHundredTwentySevenDU_47743, prime_oneHundredTwentySevenDU_52318543, prime_oneHundredTwentySevenDU_6054083257217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923258 : Nat.totient 150147894281058448293942923258 = 66664780702921013159508698880 := by
  rw [← show ((([(2, 1), (11, 1), (59, 1), (157, 1), (419687, 1), (131981867, 1), (13301637757, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_11, prime_oneHundredTwentySevenDU_59, prime_oneHundredTwentySevenDU_157, prime_oneHundredTwentySevenDU_419687, prime_oneHundredTwentySevenDU_131981867, prime_oneHundredTwentySevenDU_13301637757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923259 : Nat.totient 150147894281058448293942923259 = 97657166993947544970306604800 := by
  rw [← show ((([(3, 1), (41, 1), (5388579181, 1), (226537375929278693, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_41, prime_oneHundredTwentySevenDU_5388579181, prime_oneHundredTwentySevenDU_226537375929278693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923260 : Nat.totient 150147894281058448293942923260 = 60059157712423379317577169296 := by
  rw [← show ((([(2, 2), (5, 1), (7507394714052922414697146163, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_7507394714052922414697146163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923261 : Nat.totient 150147894281058448293942923261 = 149712691520248161460461916720 := by
  rw [← show ((([(419, 1), (1949, 1), (183862594343171454786731, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_419, prime_oneHundredTwentySevenDU_1949, prime_oneHundredTwentySevenDU_183862594343171454786731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923262 : Nat.totient 150147894281058448293942923262 = 42899370095438603850262199040 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (1521781, 1), (534167129, 1), (4397852289839, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_1521781, prime_oneHundredTwentySevenDU_534167129, prime_oneHundredTwentySevenDU_4397852289839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923263 : Nat.totient 150147894281058448293942923263 = 149140190292594968775191628328 := by
  rw [← show ((([(149, 1), (1007703988463479518751294787, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_149, prime_oneHundredTwentySevenDU_1007703988463479518751294787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923264 : Nat.totient 150147894281058448293942923264 = 75073947140440261451760107520 := by
  rw [← show ((([(2, 12), (860944894189, 1), (42577871126981, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_860944894189, prime_oneHundredTwentySevenDU_42577871126981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923265 : Nat.totient 150147894281058448293942923265 = 80078783765686605513062968320 := by
  rw [← show ((([(3, 4), (5, 1), (859361, 1), (431408385340633584733, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_859361, prime_oneHundredTwentySevenDU_431408385340633584733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923266 : Nat.totient 150147894281058448293942923266 = 65058754997092851452133043200 := by
  rw [← show ((([(2, 1), (13, 1), (19, 1), (191, 1), (263, 1), (71471, 1), (84659036714490673, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_13, prime_oneHundredTwentySevenDU_19, prime_oneHundredTwentySevenDU_191, prime_oneHundredTwentySevenDU_263, prime_oneHundredTwentySevenDU_71471, prime_oneHundredTwentySevenDU_84659036714490673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923267 : Nat.totient 150147894281058448293942923267 = 135556921987536948828413460480 := by
  rw [← show ((([(17, 1), (37, 1), (71, 1), (63997, 1), (189653, 1), (277007111612593, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_17, prime_oneHundredTwentySevenDU_37, prime_oneHundredTwentySevenDU_71, prime_oneHundredTwentySevenDU_63997, prime_oneHundredTwentySevenDU_189653, prime_oneHundredTwentySevenDU_277007111612593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923268 : Nat.totient 150147894281058448293942923268 = 49956175845031171685997202560 := by
  rw [← show ((([(2, 2), (3, 1), (541, 1), (82039, 1), (67201723, 1), (4195077308707, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_541, prime_oneHundredTwentySevenDU_82039, prime_oneHundredTwentySevenDU_67201723, prime_oneHundredTwentySevenDU_4195077308707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923269 : Nat.totient 150147894281058448293942923269 = 116996185014710401212763008960 := by
  rw [← show ((([(7, 1), (11, 1), (53813, 1), (36236088919048539734869, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_11, prime_oneHundredTwentySevenDU_53813, prime_oneHundredTwentySevenDU_36236088919048539734869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923270 : Nat.totient 150147894281058448293942923270 = 57546201955528939734513792000 := by
  rw [← show ((([(2, 1), (5, 1), (31, 1), (101, 1), (572329, 1), (8378965959427830973, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_31, prime_oneHundredTwentySevenDU_101, prime_oneHundredTwentySevenDU_572329, prime_oneHundredTwentySevenDU_8378965959427830973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923271 : Nat.totient 150147894281058448293942923271 = 100087012042212510309192929280 := by
  rw [← show ((([(3, 1), (8641, 1), (416563034933, 1), (13904432151769, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_8641, prime_oneHundredTwentySevenDU_416563034933, prime_oneHundredTwentySevenDU_13904432151769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923272 : Nat.totient 150147894281058448293942923272 = 74893542285048126900947251200 := by
  rw [← show ((([(2, 3), (431, 1), (12043, 1), (52429538753, 1), (68966988941, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_431, prime_oneHundredTwentySevenDU_12043, prime_oneHundredTwentySevenDU_52429538753, prime_oneHundredTwentySevenDU_68966988941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923273 : Nat.totient 150147894281058448293942923273 = 149067693602777452263051247428 := by
  rw [← show ((([(139, 1), (1080200678280996030891675707, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_139, prime_oneHundredTwentySevenDU_1080200678280996030891675707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923274 : Nat.totient 150147894281058448293942923274 = 50049164030791974388656617448 := by
  rw [← show ((([(2, 1), (3, 2), (373327, 1), (22343815695840442575059, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_373327, prime_oneHundredTwentySevenDU_22343815695840442575059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923275 : Nat.totient 150147894281058448293942923275 = 115976304548009421129825469440 := by
  rw [← show ((([(5, 2), (29, 1), (983407990783, 1), (210594733596833, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_29, prime_oneHundredTwentySevenDU_983407990783, prime_oneHundredTwentySevenDU_210594733596833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923276 : Nat.totient 150147894281058448293942923276 = 64349093280106920469763779200 := by
  rw [← show ((([(2, 2), (7, 1), (15252667, 1), (1291981321, 1), (272119203431, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_15252667, prime_oneHundredTwentySevenDU_1291981321, prime_oneHundredTwentySevenDU_272119203431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923277 : Nat.totient 150147894281058448293942923277 = 99900318232679341147245579456 := by
  rw [← show ((([(3, 1), (523, 1), (14653, 1), (1499167, 1), (4356319647302383, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_523, prime_oneHundredTwentySevenDU_14653, prime_oneHundredTwentySevenDU_1499167, prime_oneHundredTwentySevenDU_4356319647302383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923278 : Nat.totient 150147894281058448293942923278 = 75036466388087621938211114424 := by
  rw [← show ((([(2, 1), (2003, 1), (37480752441602208760345213, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_2003, prime_oneHundredTwentySevenDU_37480752441602208760345213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923279 : Nat.totient 150147894281058448293942923279 = 130602708717463563678680444928 := by
  rw [← show ((([(13, 1), (23, 1), (73, 1), (853, 1), (8064476232237745935409, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_13, prime_oneHundredTwentySevenDU_23, prime_oneHundredTwentySevenDU_73, prime_oneHundredTwentySevenDU_853, prime_oneHundredTwentySevenDU_8064476232237745935409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923280 : Nat.totient 150147894281058448293942923280 = 36019532956910499485932584960 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (11, 1), (97, 1), (12037, 1), (36713, 1), (49333, 1), (26894775517, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_11, prime_oneHundredTwentySevenDU_97, prime_oneHundredTwentySevenDU_12037, prime_oneHundredTwentySevenDU_36713, prime_oneHundredTwentySevenDU_49333, prime_oneHundredTwentySevenDU_26894775517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923281 : Nat.totient 150147894281058448293942923281 = 150145522916109020134406829360 := by
  rw [← show ((([(63331, 1), (287978773, 1), (8232702527553487, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_63331, prime_oneHundredTwentySevenDU_287978773, prime_oneHundredTwentySevenDU_8232702527553487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923282 : Nat.totient 150147894281058448293942923282 = 75073905201440137440786426900 := by
  rw [← show ((([(2, 1), (1790071, 1), (41939089086706183244671, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_1790071, prime_oneHundredTwentySevenDU_41939089086706183244671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923283 : Nat.totient 150147894281058448293942923283 = 85798796216925633318834390000 := by
  rw [← show ((([(3, 2), (7, 1), (166564751, 1), (14308549047229986691, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_166564751, prime_oneHundredTwentySevenDU_14308549047229986691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923284 : Nat.totient 150147894281058448293942923284 = 70657735505322269945266560000 := by
  rw [← show ((([(2, 2), (17, 1), (1043401, 1), (2405063, 1), (879898601603851, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_17, prime_oneHundredTwentySevenDU_1043401, prime_oneHundredTwentySevenDU_2405063, prime_oneHundredTwentySevenDU_879898601603851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923285 : Nat.totient 150147894281058448293942923285 = 113753753353210569912322454016 := by
  rw [← show ((([(5, 1), (19, 1), (4073, 1), (7789, 1), (49819518600249863999, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_19, prime_oneHundredTwentySevenDU_4073, prime_oneHundredTwentySevenDU_7789, prime_oneHundredTwentySevenDU_49819518600249863999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923286 : Nat.totient 150147894281058448293942923286 = 50045587164784712036086927464 := by
  rw [← show ((([(2, 1), (3, 1), (13487, 1), (1855464450718697613676663, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_13487, prime_oneHundredTwentySevenDU_1855464450718697613676663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923287 : Nat.totient 150147894281058448293942923287 = 150134010670698794970759590880 := by
  rw [← show ((([(10831, 1), (7211429, 1), (1922336260670414213, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_10831, prime_oneHundredTwentySevenDU_7211429, prime_oneHundredTwentySevenDU_1922336260670414213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923288 : Nat.totient 150147894281058448293942923288 = 74123644010912353184787253248 := by
  rw [← show ((([(2, 3), (79, 1), (59028652493, 1), (4024753607893313, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_79, prime_oneHundredTwentySevenDU_59028652493, prime_oneHundredTwentySevenDU_4024753607893313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923289 : Nat.totient 150147894281058448293942923289 = 100098596187372298862628615524 := by
  rw [← show ((([(3, 1), (50049298093686149431314307763, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_50049298093686149431314307763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923290 : Nat.totient 150147894281058448293942923290 = 51479230894390484632181724864 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (1091939, 1), (1964367898115952425573, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_1091939, prime_oneHundredTwentySevenDU_1964367898115952425573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923291 : Nat.totient 150147894281058448293942923291 = 133323667796454093176444106720 := by
  rw [← show ((([(11, 1), (43, 1), (3042023, 1), (104350758895652842229, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_11, prime_oneHundredTwentySevenDU_43, prime_oneHundredTwentySevenDU_3042023, prime_oneHundredTwentySevenDU_104350758895652842229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923292 : Nat.totient 150147894281058448293942923292 = 46198474989065544241961164800 := by
  rw [← show ((([(2, 2), (3, 3), (13, 1), (52673, 1), (2030318087912754626201, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_13, prime_oneHundredTwentySevenDU_52673, prime_oneHundredTwentySevenDU_2030318087912754626201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923293 : Nat.totient 150147894281058448293942923293 = 150146929606029891292335541824 := by
  rw [← show ((([(173573, 1), (1506997, 1), (574016912460446453, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_173573, prime_oneHundredTwentySevenDU_1506997, prime_oneHundredTwentySevenDU_574016912460446453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923294 : Nat.totient 150147894281058448293942923294 = 75073947140529224146971461646 := by
  rw [← show ((([(2, 1), (75073947140529224146971461647, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_75073947140529224146971461647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923295 : Nat.totient 150147894281058448293942923295 = 79466782640185008653764608000 := by
  rw [← show ((([(3, 1), (5, 1), (131, 1), (157519, 1), (300569, 1), (2196401, 1), (734797933, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_131, prime_oneHundredTwentySevenDU_157519, prime_oneHundredTwentySevenDU_300569, prime_oneHundredTwentySevenDU_2196401, prime_oneHundredTwentySevenDU_734797933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923296 : Nat.totient 150147894281058448293942923296 = 75073076908568881847097120000 := by
  rw [← show ((([(2, 5), (86269, 1), (76422058751, 1), (711698041387, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_86269, prime_oneHundredTwentySevenDU_76422058751, prime_oneHundredTwentySevenDU_711698041387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923297 : Nat.totient 150147894281058448293942923297 = 128565090441955165377622118400 := by
  rw [← show ((([(7, 4), (1549, 1), (2621, 1), (145661, 1), (2013049, 1), (52530437, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_7, prime_oneHundredTwentySevenDU_1549, prime_oneHundredTwentySevenDU_2621, prime_oneHundredTwentySevenDU_145661, prime_oneHundredTwentySevenDU_2013049, prime_oneHundredTwentySevenDU_52530437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923298 : Nat.totient 150147894281058448293942923298 = 48929629002276663724760962560 := by
  rw [← show ((([(2, 1), (3, 1), (47, 1), (1019, 1), (7283, 1), (595873081, 1), (120401494397, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_47, prime_oneHundredTwentySevenDU_1019, prime_oneHundredTwentySevenDU_7283, prime_oneHundredTwentySevenDU_595873081, prime_oneHundredTwentySevenDU_120401494397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923299 : Nat.totient 150147894281058448293942923299 = 146361855107700632789517376512 := by
  rw [← show ((([(67, 1), (167, 1), (223, 1), (2154329, 1), (27932581935222673, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_67, prime_oneHundredTwentySevenDU_167, prime_oneHundredTwentySevenDU_223, prime_oneHundredTwentySevenDU_2154329, prime_oneHundredTwentySevenDU_27932581935222673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923300 : Nat.totient 150147894281058448293942923300 = 57632667027886134063639168000 := by
  rw [← show ((([(2, 2), (5, 2), (41, 1), (61, 1), (53819, 1), (11155009133384380007, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_2, prime_oneHundredTwentySevenDU_5, prime_oneHundredTwentySevenDU_41, prime_oneHundredTwentySevenDU_61, prime_oneHundredTwentySevenDU_53819, prime_oneHundredTwentySevenDU_11155009133384380007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySevenDU_150147894281058448293942923301 : Nat.totient 150147894281058448293942923301 = 89450702448144394540710758400 := by
  rw [← show ((([(3, 2), (17, 1), (31, 1), (53, 1), (186581, 1), (3201273910488331499, 1)] : List FactorBlock).map factorBlockValue).prod) = 150147894281058448293942923301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySevenDU_3, prime_oneHundredTwentySevenDU_17, prime_oneHundredTwentySevenDU_31, prime_oneHundredTwentySevenDU_53, prime_oneHundredTwentySevenDU_186581, prime_oneHundredTwentySevenDU_3201273910488331499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwentySevenDU : certifiedKill 1 150147894281058448293942923199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwentySevenDU_150147894281058448293942923200, phi_oneHundredTwentySevenDU_150147894281058448293942923201, phi_oneHundredTwentySevenDU_150147894281058448293942923202,
    phi_oneHundredTwentySevenDU_150147894281058448293942923203, phi_oneHundredTwentySevenDU_150147894281058448293942923204, phi_oneHundredTwentySevenDU_150147894281058448293942923205,
    phi_oneHundredTwentySevenDU_150147894281058448293942923206, phi_oneHundredTwentySevenDU_150147894281058448293942923207, phi_oneHundredTwentySevenDU_150147894281058448293942923208,
    phi_oneHundredTwentySevenDU_150147894281058448293942923209, phi_oneHundredTwentySevenDU_150147894281058448293942923210, phi_oneHundredTwentySevenDU_150147894281058448293942923211,
    phi_oneHundredTwentySevenDU_150147894281058448293942923212, phi_oneHundredTwentySevenDU_150147894281058448293942923213, phi_oneHundredTwentySevenDU_150147894281058448293942923214,
    phi_oneHundredTwentySevenDU_150147894281058448293942923215, phi_oneHundredTwentySevenDU_150147894281058448293942923216, phi_oneHundredTwentySevenDU_150147894281058448293942923217,
    phi_oneHundredTwentySevenDU_150147894281058448293942923218, phi_oneHundredTwentySevenDU_150147894281058448293942923219, phi_oneHundredTwentySevenDU_150147894281058448293942923220,
    phi_oneHundredTwentySevenDU_150147894281058448293942923221, phi_oneHundredTwentySevenDU_150147894281058448293942923222, phi_oneHundredTwentySevenDU_150147894281058448293942923223,
    phi_oneHundredTwentySevenDU_150147894281058448293942923224, phi_oneHundredTwentySevenDU_150147894281058448293942923225, phi_oneHundredTwentySevenDU_150147894281058448293942923226,
    phi_oneHundredTwentySevenDU_150147894281058448293942923227, phi_oneHundredTwentySevenDU_150147894281058448293942923228, phi_oneHundredTwentySevenDU_150147894281058448293942923229,
    phi_oneHundredTwentySevenDU_150147894281058448293942923230, phi_oneHundredTwentySevenDU_150147894281058448293942923231, phi_oneHundredTwentySevenDU_150147894281058448293942923232,
    phi_oneHundredTwentySevenDU_150147894281058448293942923233, phi_oneHundredTwentySevenDU_150147894281058448293942923234, phi_oneHundredTwentySevenDU_150147894281058448293942923235,
    phi_oneHundredTwentySevenDU_150147894281058448293942923236, phi_oneHundredTwentySevenDU_150147894281058448293942923237, phi_oneHundredTwentySevenDU_150147894281058448293942923238,
    phi_oneHundredTwentySevenDU_150147894281058448293942923239, phi_oneHundredTwentySevenDU_150147894281058448293942923240, phi_oneHundredTwentySevenDU_150147894281058448293942923241,
    phi_oneHundredTwentySevenDU_150147894281058448293942923242, phi_oneHundredTwentySevenDU_150147894281058448293942923243, phi_oneHundredTwentySevenDU_150147894281058448293942923244,
    phi_oneHundredTwentySevenDU_150147894281058448293942923245, phi_oneHundredTwentySevenDU_150147894281058448293942923246, phi_oneHundredTwentySevenDU_150147894281058448293942923247,
    phi_oneHundredTwentySevenDU_150147894281058448293942923248, phi_oneHundredTwentySevenDU_150147894281058448293942923249, phi_oneHundredTwentySevenDU_150147894281058448293942923250,
    phi_oneHundredTwentySevenDU_150147894281058448293942923251, phi_oneHundredTwentySevenDU_150147894281058448293942923252, phi_oneHundredTwentySevenDU_150147894281058448293942923253,
    phi_oneHundredTwentySevenDU_150147894281058448293942923254, phi_oneHundredTwentySevenDU_150147894281058448293942923255, phi_oneHundredTwentySevenDU_150147894281058448293942923256,
    phi_oneHundredTwentySevenDU_150147894281058448293942923257, phi_oneHundredTwentySevenDU_150147894281058448293942923258, phi_oneHundredTwentySevenDU_150147894281058448293942923259,
    phi_oneHundredTwentySevenDU_150147894281058448293942923260, phi_oneHundredTwentySevenDU_150147894281058448293942923261, phi_oneHundredTwentySevenDU_150147894281058448293942923262,
    phi_oneHundredTwentySevenDU_150147894281058448293942923263, phi_oneHundredTwentySevenDU_150147894281058448293942923264, phi_oneHundredTwentySevenDU_150147894281058448293942923265,
    phi_oneHundredTwentySevenDU_150147894281058448293942923266, phi_oneHundredTwentySevenDU_150147894281058448293942923267, phi_oneHundredTwentySevenDU_150147894281058448293942923268,
    phi_oneHundredTwentySevenDU_150147894281058448293942923269, phi_oneHundredTwentySevenDU_150147894281058448293942923270, phi_oneHundredTwentySevenDU_150147894281058448293942923271,
    phi_oneHundredTwentySevenDU_150147894281058448293942923272, phi_oneHundredTwentySevenDU_150147894281058448293942923273, phi_oneHundredTwentySevenDU_150147894281058448293942923274,
    phi_oneHundredTwentySevenDU_150147894281058448293942923275, phi_oneHundredTwentySevenDU_150147894281058448293942923276, phi_oneHundredTwentySevenDU_150147894281058448293942923277,
    phi_oneHundredTwentySevenDU_150147894281058448293942923278, phi_oneHundredTwentySevenDU_150147894281058448293942923279, phi_oneHundredTwentySevenDU_150147894281058448293942923280,
    phi_oneHundredTwentySevenDU_150147894281058448293942923281, phi_oneHundredTwentySevenDU_150147894281058448293942923282, phi_oneHundredTwentySevenDU_150147894281058448293942923283,
    phi_oneHundredTwentySevenDU_150147894281058448293942923284, phi_oneHundredTwentySevenDU_150147894281058448293942923285, phi_oneHundredTwentySevenDU_150147894281058448293942923286,
    phi_oneHundredTwentySevenDU_150147894281058448293942923287, phi_oneHundredTwentySevenDU_150147894281058448293942923288, phi_oneHundredTwentySevenDU_150147894281058448293942923289,
    phi_oneHundredTwentySevenDU_150147894281058448293942923290, phi_oneHundredTwentySevenDU_150147894281058448293942923291, phi_oneHundredTwentySevenDU_150147894281058448293942923292,
    phi_oneHundredTwentySevenDU_150147894281058448293942923293, phi_oneHundredTwentySevenDU_150147894281058448293942923294, phi_oneHundredTwentySevenDU_150147894281058448293942923295,
    phi_oneHundredTwentySevenDU_150147894281058448293942923296, phi_oneHundredTwentySevenDU_150147894281058448293942923297, phi_oneHundredTwentySevenDU_150147894281058448293942923298,
    phi_oneHundredTwentySevenDU_150147894281058448293942923299, phi_oneHundredTwentySevenDU_150147894281058448293942923300, phi_oneHundredTwentySevenDU_150147894281058448293942923301
    ]

end TotientTailPeriodKiller
end Erdos249257
