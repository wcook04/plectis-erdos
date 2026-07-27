import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredSixtySixFHFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixtySixFHFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixtySixFHFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixtySixFHFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixtySixFHFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixtySixFHFastPow a n * oneHundredSixtySixFHFastPow a n * a else oneHundredSixtySixFHFastPow a n * oneHundredSixtySixFHFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixtySixFH_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredSixtySixFH_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredSixtySixFH_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredSixtySixFH_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredSixtySixFH_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredSixtySixFH_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredSixtySixFH_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredSixtySixFH_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredSixtySixFH_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredSixtySixFH_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredSixtySixFH_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredSixtySixFH_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredSixtySixFH_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredSixtySixFH_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredSixtySixFH_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredSixtySixFH_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredSixtySixFH_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredSixtySixFH_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredSixtySixFH_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredSixtySixFH_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredSixtySixFH_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredSixtySixFH_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredSixtySixFH_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredSixtySixFH_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredSixtySixFH_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredSixtySixFH_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredSixtySixFH_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredSixtySixFH_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredSixtySixFH_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredSixtySixFH_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredSixtySixFH_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredSixtySixFH_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredSixtySixFH_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredSixtySixFH_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredSixtySixFH_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredSixtySixFH_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredSixtySixFH_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredSixtySixFH_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredSixtySixFH_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredSixtySixFH_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredSixtySixFH_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredSixtySixFH_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredSixtySixFH_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredSixtySixFH_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredSixtySixFH_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredSixtySixFH_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredSixtySixFH_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredSixtySixFH_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredSixtySixFH_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredSixtySixFH_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredSixtySixFH_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredSixtySixFH_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredSixtySixFH_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredSixtySixFH_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredSixtySixFH_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredSixtySixFH_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredSixtySixFH_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredSixtySixFH_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredSixtySixFH_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredSixtySixFH_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredSixtySixFH_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredSixtySixFH_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredSixtySixFH_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredSixtySixFH_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredSixtySixFH_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredSixtySixFH_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredSixtySixFH_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredSixtySixFH_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredSixtySixFH_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredSixtySixFH_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredSixtySixFH_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredSixtySixFH_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredSixtySixFH_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredSixtySixFH_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredSixtySixFH_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredSixtySixFH_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredSixtySixFH_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredSixtySixFH_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredSixtySixFH_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredSixtySixFH_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredSixtySixFH_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredSixtySixFH_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredSixtySixFH_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredSixtySixFH_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredSixtySixFH_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredSixtySixFH_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredSixtySixFH_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredSixtySixFH_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredSixtySixFH_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredSixtySixFH_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredSixtySixFH_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredSixtySixFH_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredSixtySixFH_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredSixtySixFH_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredSixtySixFH_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredSixtySixFH_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredSixtySixFH_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredSixtySixFH_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredSixtySixFH_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredSixtySixFH_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredSixtySixFH_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredSixtySixFH_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredSixtySixFH_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredSixtySixFH_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredSixtySixFH_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredSixtySixFH_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredSixtySixFH_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredSixtySixFH_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredSixtySixFH_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredSixtySixFH_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredSixtySixFH_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredSixtySixFH_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredSixtySixFH_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredSixtySixFH_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredSixtySixFH_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredSixtySixFH_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredSixtySixFH_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredSixtySixFH_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredSixtySixFH_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredSixtySixFH_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredSixtySixFH_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredSixtySixFH_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredSixtySixFH_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredSixtySixFH_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_oneHundredSixtySixFH_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredSixtySixFH_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredSixtySixFH_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredSixtySixFH_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredSixtySixFH_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredSixtySixFH_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredSixtySixFH_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredSixtySixFH_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredSixtySixFH_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredSixtySixFH_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredSixtySixFH_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredSixtySixFH_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_oneHundredSixtySixFH_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredSixtySixFH_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredSixtySixFH_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_oneHundredSixtySixFH_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_oneHundredSixtySixFH_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredSixtySixFH_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredSixtySixFH_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_oneHundredSixtySixFH_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredSixtySixFH_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredSixtySixFH_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredSixtySixFH_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredSixtySixFH_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredSixtySixFH_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredSixtySixFH_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_oneHundredSixtySixFH_1949 : Nat.Prime 1949 := by norm_num

private theorem prime_oneHundredSixtySixFH_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_oneHundredSixtySixFH_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_oneHundredSixtySixFH_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_oneHundredSixtySixFH_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_oneHundredSixtySixFH_2341 : Nat.Prime 2341 := by norm_num

private theorem prime_oneHundredSixtySixFH_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_oneHundredSixtySixFH_2557 : Nat.Prime 2557 := by norm_num

private theorem prime_oneHundredSixtySixFH_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_oneHundredSixtySixFH_2687 : Nat.Prime 2687 := by norm_num

private theorem prime_oneHundredSixtySixFH_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_oneHundredSixtySixFH_3023 : Nat.Prime 3023 := by norm_num

private theorem prime_oneHundredSixtySixFH_3041 : Nat.Prime 3041 := by norm_num

private theorem prime_oneHundredSixtySixFH_3089 : Nat.Prime 3089 := by norm_num

private theorem prime_oneHundredSixtySixFH_3203 : Nat.Prime 3203 := by norm_num

private theorem prime_oneHundredSixtySixFH_3209 : Nat.Prime 3209 := by norm_num

private theorem prime_oneHundredSixtySixFH_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredSixtySixFH_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_oneHundredSixtySixFH_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_oneHundredSixtySixFH_3469 : Nat.Prime 3469 := by norm_num

private theorem prime_oneHundredSixtySixFH_3539 : Nat.Prime 3539 := by norm_num

private theorem prime_oneHundredSixtySixFH_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_oneHundredSixtySixFH_3691 : Nat.Prime 3691 := by norm_num

private theorem prime_oneHundredSixtySixFH_3701 : Nat.Prime 3701 := by norm_num

private theorem prime_oneHundredSixtySixFH_3739 : Nat.Prime 3739 := by norm_num

private theorem prime_oneHundredSixtySixFH_3761 : Nat.Prime 3761 := by norm_num

private theorem prime_oneHundredSixtySixFH_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_oneHundredSixtySixFH_3877 : Nat.Prime 3877 := by norm_num

private theorem prime_oneHundredSixtySixFH_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_oneHundredSixtySixFH_3943 : Nat.Prime 3943 := by norm_num

private theorem prime_oneHundredSixtySixFH_4019 : Nat.Prime 4019 := by norm_num

private theorem prime_oneHundredSixtySixFH_4049 : Nat.Prime 4049 := by norm_num

private theorem prime_oneHundredSixtySixFH_4211 : Nat.Prime 4211 := by norm_num

private theorem prime_oneHundredSixtySixFH_4231 : Nat.Prime 4231 := by norm_num

private theorem prime_oneHundredSixtySixFH_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_oneHundredSixtySixFH_4261 : Nat.Prime 4261 := by norm_num

private theorem prime_oneHundredSixtySixFH_4271 : Nat.Prime 4271 := by norm_num

private theorem prime_oneHundredSixtySixFH_4493 : Nat.Prime 4493 := by norm_num

private theorem prime_oneHundredSixtySixFH_4831 : Nat.Prime 4831 := by norm_num

private theorem prime_oneHundredSixtySixFH_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_oneHundredSixtySixFH_5231 : Nat.Prime 5231 := by norm_num

private theorem prime_oneHundredSixtySixFH_5449 : Nat.Prime 5449 := by norm_num

private theorem prime_oneHundredSixtySixFH_5737 : Nat.Prime 5737 := by norm_num

private theorem prime_oneHundredSixtySixFH_6257 : Nat.Prime 6257 := by norm_num

private theorem prime_oneHundredSixtySixFH_6269 : Nat.Prime 6269 := by norm_num

private theorem prime_oneHundredSixtySixFH_6529 : Nat.Prime 6529 := by norm_num

private theorem prime_oneHundredSixtySixFH_6653 : Nat.Prime 6653 := by norm_num

private theorem prime_oneHundredSixtySixFH_6991 : Nat.Prime 6991 := by norm_num

private theorem prime_oneHundredSixtySixFH_7109 : Nat.Prime 7109 := by norm_num

private theorem prime_oneHundredSixtySixFH_7127 : Nat.Prime 7127 := by norm_num

private theorem prime_oneHundredSixtySixFH_7307 : Nat.Prime 7307 := by norm_num

private theorem prime_oneHundredSixtySixFH_7369 : Nat.Prime 7369 := by norm_num

private theorem prime_oneHundredSixtySixFH_7529 : Nat.Prime 7529 := by norm_num

private theorem prime_oneHundredSixtySixFH_8059 : Nat.Prime 8059 := by norm_num

private theorem prime_oneHundredSixtySixFH_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredSixtySixFH_8839 : Nat.Prime 8839 := by norm_num

private theorem prime_oneHundredSixtySixFH_9013 : Nat.Prime 9013 := by norm_num

private theorem prime_oneHundredSixtySixFH_9281 : Nat.Prime 9281 := by norm_num

private theorem prime_oneHundredSixtySixFH_9511 : Nat.Prime 9511 := by norm_num

private theorem prime_oneHundredSixtySixFH_9623 : Nat.Prime 9623 := by norm_num

private theorem prime_oneHundredSixtySixFH_10253 : Nat.Prime 10253 := by norm_num

private theorem prime_oneHundredSixtySixFH_10357 : Nat.Prime 10357 := by norm_num

private theorem prime_oneHundredSixtySixFH_10639 : Nat.Prime 10639 := by norm_num

private theorem prime_oneHundredSixtySixFH_10667 : Nat.Prime 10667 := by norm_num

private theorem prime_oneHundredSixtySixFH_11117 : Nat.Prime 11117 := by norm_num

private theorem prime_oneHundredSixtySixFH_13799 : Nat.Prime 13799 := by norm_num

private theorem prime_oneHundredSixtySixFH_13879 : Nat.Prime 13879 := by norm_num

private theorem prime_oneHundredSixtySixFH_14887 : Nat.Prime 14887 := by norm_num

private theorem prime_oneHundredSixtySixFH_14951 : Nat.Prime 14951 := by norm_num

private theorem prime_oneHundredSixtySixFH_14969 : Nat.Prime 14969 := by norm_num

private theorem prime_oneHundredSixtySixFH_15671 : Nat.Prime 15671 := by norm_num

private theorem prime_oneHundredSixtySixFH_15907 : Nat.Prime 15907 := by norm_num

private theorem prime_oneHundredSixtySixFH_17117 : Nat.Prime 17117 := by norm_num

private theorem prime_oneHundredSixtySixFH_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredSixtySixFH_17509 : Nat.Prime 17509 := by norm_num

private theorem prime_oneHundredSixtySixFH_17837 : Nat.Prime 17837 := by norm_num

private theorem prime_oneHundredSixtySixFH_18043 : Nat.Prime 18043 := by norm_num

private theorem prime_oneHundredSixtySixFH_18749 : Nat.Prime 18749 := by norm_num

private theorem prime_oneHundredSixtySixFH_18913 : Nat.Prime 18913 := by norm_num

private theorem prime_oneHundredSixtySixFH_19013 : Nat.Prime 19013 := by norm_num

private theorem prime_oneHundredSixtySixFH_19717 : Nat.Prime 19717 := by norm_num

private theorem prime_oneHundredSixtySixFH_19949 : Nat.Prime 19949 := by norm_num

private theorem prime_oneHundredSixtySixFH_20107 : Nat.Prime 20107 := by norm_num

private theorem prime_oneHundredSixtySixFH_20641 : Nat.Prime 20641 := by norm_num

private theorem prime_oneHundredSixtySixFH_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredSixtySixFH_20929 : Nat.Prime 20929 := by norm_num

private theorem prime_oneHundredSixtySixFH_21587 : Nat.Prime 21587 := by norm_num

private theorem prime_oneHundredSixtySixFH_22271 : Nat.Prime 22271 := by norm_num

private theorem prime_oneHundredSixtySixFH_22717 : Nat.Prime 22717 := by norm_num

private theorem prime_oneHundredSixtySixFH_25147 : Nat.Prime 25147 := by norm_num

private theorem prime_oneHundredSixtySixFH_27997 : Nat.Prime 27997 := by norm_num

private theorem prime_oneHundredSixtySixFH_28307 : Nat.Prime 28307 := by norm_num

private theorem prime_oneHundredSixtySixFH_29383 : Nat.Prime 29383 := by norm_num

private theorem prime_oneHundredSixtySixFH_29429 : Nat.Prime 29429 := by norm_num

private theorem prime_oneHundredSixtySixFH_31513 : Nat.Prime 31513 := by norm_num

private theorem prime_oneHundredSixtySixFH_31547 : Nat.Prime 31547 := by norm_num

private theorem prime_oneHundredSixtySixFH_31963 : Nat.Prime 31963 := by norm_num

private theorem prime_oneHundredSixtySixFH_32089 : Nat.Prime 32089 := by norm_num

private theorem prime_oneHundredSixtySixFH_32213 : Nat.Prime 32213 := by norm_num

private theorem prime_oneHundredSixtySixFH_32611 : Nat.Prime 32611 := by norm_num

private theorem prime_oneHundredSixtySixFH_33427 : Nat.Prime 33427 := by norm_num

private theorem prime_oneHundredSixtySixFH_33619 : Nat.Prime 33619 := by norm_num

private theorem prime_oneHundredSixtySixFH_34583 : Nat.Prime 34583 := by norm_num

private theorem prime_oneHundredSixtySixFH_34667 : Nat.Prime 34667 := by norm_num

private theorem prime_oneHundredSixtySixFH_35869 : Nat.Prime 35869 := by norm_num

private theorem prime_oneHundredSixtySixFH_37993 : Nat.Prime 37993 := by norm_num

private theorem prime_oneHundredSixtySixFH_38567 : Nat.Prime 38567 := by norm_num

private theorem prime_oneHundredSixtySixFH_40583 : Nat.Prime 40583 := by norm_num

private theorem prime_oneHundredSixtySixFH_41737 : Nat.Prime 41737 := by norm_num

private theorem prime_oneHundredSixtySixFH_41849 : Nat.Prime 41849 := by norm_num

private theorem prime_oneHundredSixtySixFH_42937 : Nat.Prime 42937 := by norm_num

private theorem prime_oneHundredSixtySixFH_47497 : Nat.Prime 47497 := by norm_num

private theorem prime_oneHundredSixtySixFH_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredSixtySixFH_50023 : Nat.Prime 50023 := by norm_num

private theorem prime_oneHundredSixtySixFH_50291 : Nat.Prime 50291 := by norm_num

private theorem prime_oneHundredSixtySixFH_50909 : Nat.Prime 50909 := by norm_num

private theorem prime_oneHundredSixtySixFH_51769 : Nat.Prime 51769 := by norm_num

private theorem prime_oneHundredSixtySixFH_52237 : Nat.Prime 52237 := by norm_num

private theorem prime_oneHundredSixtySixFH_56941 : Nat.Prime 56941 := by norm_num

private theorem prime_oneHundredSixtySixFH_58579 : Nat.Prime 58579 := by norm_num

private theorem prime_oneHundredSixtySixFH_61643 : Nat.Prime 61643 := by norm_num

private theorem prime_oneHundredSixtySixFH_63997 : Nat.Prime 63997 := by norm_num

private theorem prime_oneHundredSixtySixFH_64123 : Nat.Prime 64123 := by norm_num

private theorem prime_oneHundredSixtySixFH_64171 : Nat.Prime 64171 := by norm_num

private theorem prime_oneHundredSixtySixFH_65167 : Nat.Prime 65167 := by norm_num

private theorem prime_oneHundredSixtySixFH_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredSixtySixFH_71411 : Nat.Prime 71411 := by norm_num

private theorem prime_oneHundredSixtySixFH_74623 : Nat.Prime 74623 := by norm_num

private theorem prime_oneHundredSixtySixFH_77191 : Nat.Prime 77191 := by norm_num

private theorem prime_oneHundredSixtySixFH_81853 : Nat.Prime 81853 := by norm_num

private theorem prime_oneHundredSixtySixFH_87877 : Nat.Prime 87877 := by norm_num

private theorem prime_oneHundredSixtySixFH_90697 : Nat.Prime 90697 := by norm_num

private theorem prime_oneHundredSixtySixFH_94291 : Nat.Prime 94291 := by norm_num

private theorem prime_oneHundredSixtySixFH_95891 : Nat.Prime 95891 := by norm_num

private theorem prime_oneHundredSixtySixFH_97883 : Nat.Prime 97883 := by norm_num

private theorem prime_oneHundredSixtySixFH_98207 : Nat.Prime 98207 := by norm_num

private theorem prime_oneHundredSixtySixFH_98317 : Nat.Prime 98317 := by norm_num

private theorem prime_oneHundredSixtySixFH_108343 : Nat.Prime 108343 := by norm_num

private theorem prime_oneHundredSixtySixFH_108883 : Nat.Prime 108883 := by norm_num

private theorem prime_oneHundredSixtySixFH_108971 : Nat.Prime 108971 := by norm_num

private theorem prime_oneHundredSixtySixFH_110603 : Nat.Prime 110603 := by norm_num

private theorem prime_oneHundredSixtySixFH_114343 : Nat.Prime 114343 := by norm_num

private theorem prime_oneHundredSixtySixFH_117619 : Nat.Prime 117619 := by norm_num

private theorem prime_oneHundredSixtySixFH_118543 : Nat.Prime 118543 := by norm_num

private theorem prime_oneHundredSixtySixFH_122869 : Nat.Prime 122869 := by norm_num

private theorem prime_oneHundredSixtySixFH_124951 : Nat.Prime 124951 := by norm_num

private theorem prime_oneHundredSixtySixFH_127819 : Nat.Prime 127819 := by norm_num

private theorem prime_oneHundredSixtySixFH_134741 : Nat.Prime 134741 := by norm_num

private theorem prime_oneHundredSixtySixFH_136547 : Nat.Prime 136547 := by norm_num

private theorem prime_oneHundredSixtySixFH_139787 : Nat.Prime 139787 := by norm_num

private theorem prime_oneHundredSixtySixFH_140557 : Nat.Prime 140557 := by norm_num

private theorem prime_oneHundredSixtySixFH_141709 : Nat.Prime 141709 := by norm_num

private theorem prime_oneHundredSixtySixFH_142589 : Nat.Prime 142589 := by norm_num

private theorem prime_oneHundredSixtySixFH_142787 : Nat.Prime 142787 := by norm_num

private theorem prime_oneHundredSixtySixFH_144139 : Nat.Prime 144139 := by norm_num

private theorem prime_oneHundredSixtySixFH_147073 : Nat.Prime 147073 := by norm_num

private theorem prime_oneHundredSixtySixFH_149111 : Nat.Prime 149111 := by norm_num

private theorem prime_oneHundredSixtySixFH_160163 : Nat.Prime 160163 := by norm_num

private theorem prime_oneHundredSixtySixFH_164419 : Nat.Prime 164419 := by norm_num

private theorem prime_oneHundredSixtySixFH_165707 : Nat.Prime 165707 := by norm_num

private theorem prime_oneHundredSixtySixFH_165811 : Nat.Prime 165811 := by norm_num

private theorem prime_oneHundredSixtySixFH_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredSixtySixFH_183437 : Nat.Prime 183437 := by norm_num

private theorem prime_oneHundredSixtySixFH_191827 : Nat.Prime 191827 := by norm_num

private theorem prime_oneHundredSixtySixFH_197651 : Nat.Prime 197651 := by norm_num

private theorem prime_oneHundredSixtySixFH_209821 : Nat.Prime 209821 := by norm_num

private theorem prime_oneHundredSixtySixFH_210319 : Nat.Prime 210319 := by norm_num

private theorem prime_oneHundredSixtySixFH_212969 : Nat.Prime 212969 := by norm_num

private theorem prime_oneHundredSixtySixFH_215317 : Nat.Prime 215317 := by norm_num

private theorem prime_oneHundredSixtySixFH_225067 : Nat.Prime 225067 := by norm_num

private theorem prime_oneHundredSixtySixFH_227399 : Nat.Prime 227399 := by norm_num

private theorem prime_oneHundredSixtySixFH_242161 : Nat.Prime 242161 := by norm_num

private theorem prime_oneHundredSixtySixFH_263437 : Nat.Prime 263437 := by norm_num

private theorem prime_oneHundredSixtySixFH_268721 : Nat.Prime 268721 := by norm_num

private theorem prime_oneHundredSixtySixFH_268771 : Nat.Prime 268771 := by norm_num

private theorem prime_oneHundredSixtySixFH_289049 : Nat.Prime 289049 := by norm_num

private theorem prime_oneHundredSixtySixFH_298237 : Nat.Prime 298237 := by norm_num

private theorem prime_oneHundredSixtySixFH_300431 : Nat.Prime 300431 := by norm_num

private theorem prime_oneHundredSixtySixFH_304433 : Nat.Prime 304433 := by norm_num

private theorem prime_oneHundredSixtySixFH_306853 : Nat.Prime 306853 := by norm_num

private theorem prime_oneHundredSixtySixFH_311533 : Nat.Prime 311533 := by norm_num

private theorem prime_oneHundredSixtySixFH_327839 : Nat.Prime 327839 := by norm_num

private theorem prime_oneHundredSixtySixFH_328271 : Nat.Prime 328271 := by norm_num

private theorem prime_oneHundredSixtySixFH_332903 : Nat.Prime 332903 := by norm_num

private theorem prime_oneHundredSixtySixFH_333517 : Nat.Prime 333517 := by norm_num

private theorem prime_oneHundredSixtySixFH_386569 : Nat.Prime 386569 := by norm_num

private theorem prime_oneHundredSixtySixFH_416387 : Nat.Prime 416387 := by norm_num

private theorem prime_oneHundredSixtySixFH_450019 : Nat.Prime 450019 := by norm_num

private theorem prime_oneHundredSixtySixFH_490003 : Nat.Prime 490003 := by norm_num

private theorem prime_oneHundredSixtySixFH_533581 : Nat.Prime 533581 := by norm_num

private theorem prime_oneHundredSixtySixFH_556159 : Nat.Prime 556159 := by norm_num

private theorem prime_oneHundredSixtySixFH_589063 : Nat.Prime 589063 := by norm_num

private theorem prime_oneHundredSixtySixFH_603937 : Nat.Prime 603937 := by norm_num

private theorem prime_oneHundredSixtySixFH_621017 : Nat.Prime 621017 := by norm_num

private theorem prime_oneHundredSixtySixFH_660659 : Nat.Prime 660659 := by norm_num

private theorem prime_oneHundredSixtySixFH_674371 : Nat.Prime 674371 := by norm_num

private theorem prime_oneHundredSixtySixFH_677543 : Nat.Prime 677543 := by norm_num

private theorem prime_oneHundredSixtySixFH_714773 : Nat.Prime 714773 := by norm_num

private theorem prime_oneHundredSixtySixFH_730157 : Nat.Prime 730157 := by norm_num

private theorem prime_oneHundredSixtySixFH_769151 : Nat.Prime 769151 := by norm_num

private theorem prime_oneHundredSixtySixFH_811519 : Nat.Prime 811519 := by norm_num

private theorem prime_oneHundredSixtySixFH_821677 : Nat.Prime 821677 := by norm_num

private theorem prime_oneHundredSixtySixFH_840439 : Nat.Prime 840439 := by norm_num

private theorem prime_oneHundredSixtySixFH_840823 : Nat.Prime 840823 := by norm_num

private theorem prime_oneHundredSixtySixFH_861937 : Nat.Prime 861937 := by norm_num

private theorem prime_oneHundredSixtySixFH_884231 : Nat.Prime 884231 := by norm_num

private theorem prime_oneHundredSixtySixFH_903919 : Nat.Prime 903919 := by norm_num

private theorem prime_oneHundredSixtySixFH_904721 : Nat.Prime 904721 := by norm_num

private theorem prime_oneHundredSixtySixFH_968879 : Nat.Prime 968879 := by norm_num

private theorem prime_oneHundredSixtySixFH_1002569 : Nat.Prime 1002569 := by norm_num

private theorem prime_oneHundredSixtySixFH_1003609 : Nat.Prime 1003609 := by norm_num

private theorem prime_oneHundredSixtySixFH_1075787 : Nat.Prime 1075787 := by norm_num

private theorem prime_oneHundredSixtySixFH_1082243 : Nat.Prime 1082243 := by norm_num

private theorem prime_oneHundredSixtySixFH_1095119 : Nat.Prime 1095119 := by norm_num

private theorem prime_oneHundredSixtySixFH_1104739 : Nat.Prime 1104739 := by norm_num

private theorem prime_oneHundredSixtySixFH_1130497 : Nat.Prime 1130497 := by norm_num

private theorem prime_oneHundredSixtySixFH_1143959 : Nat.Prime 1143959 := by norm_num

private theorem prime_oneHundredSixtySixFH_1274209 : Nat.Prime 1274209 := by norm_num

private theorem prime_oneHundredSixtySixFH_1291453 : Nat.Prime 1291453 := by norm_num

private theorem prime_oneHundredSixtySixFH_1417561 : Nat.Prime 1417561 := by norm_num

private theorem prime_oneHundredSixtySixFH_1481527 : Nat.Prime 1481527 := by norm_num

private theorem prime_oneHundredSixtySixFH_1481947 : Nat.Prime 1481947 := by norm_num

private theorem prime_oneHundredSixtySixFH_1729157 : Nat.Prime 1729157 := by norm_num

private theorem prime_oneHundredSixtySixFH_1859521 : Nat.Prime 1859521 := by norm_num

private theorem prime_oneHundredSixtySixFH_1911149 : Nat.Prime 1911149 := by norm_num

private theorem prime_oneHundredSixtySixFH_2067937 : Nat.Prime 2067937 := by norm_num

private theorem prime_oneHundredSixtySixFH_2090173 : Nat.Prime 2090173 := by norm_num

private theorem prime_oneHundredSixtySixFH_2141261 : Nat.Prime 2141261 := by norm_num

private theorem prime_oneHundredSixtySixFH_2343889 : Nat.Prime 2343889 := by norm_num

private theorem prime_oneHundredSixtySixFH_2397949 : Nat.Prime 2397949 := by norm_num

private theorem prime_oneHundredSixtySixFH_2673577 : Nat.Prime 2673577 := by norm_num

private theorem prime_oneHundredSixtySixFH_2791837 : Nat.Prime 2791837 := by norm_num

private theorem prime_oneHundredSixtySixFH_2863453 : Nat.Prime 2863453 := by norm_num

private theorem prime_oneHundredSixtySixFH_3240529 : Nat.Prime 3240529 := by norm_num

private theorem prime_oneHundredSixtySixFH_3506549 : Nat.Prime 3506549 := by norm_num

private theorem prime_oneHundredSixtySixFH_3764149 : Nat.Prime 3764149 := by norm_num

private theorem prime_oneHundredSixtySixFH_3806119 : Nat.Prime 3806119 := by norm_num

private theorem prime_oneHundredSixtySixFH_4331939 : Nat.Prime 4331939 := by norm_num

private theorem prime_oneHundredSixtySixFH_4392719 : Nat.Prime 4392719 := by norm_num

private theorem prime_oneHundredSixtySixFH_4750831 : Nat.Prime 4750831 := by norm_num

private theorem prime_oneHundredSixtySixFH_4874273 : Nat.Prime 4874273 := by norm_num

private theorem prime_oneHundredSixtySixFH_5073139 : Nat.Prime 5073139 := by norm_num

private theorem prime_oneHundredSixtySixFH_5410901 : Nat.Prime 5410901 := by norm_num

private theorem prime_oneHundredSixtySixFH_5777279 : Nat.Prime 5777279 := by norm_num

private theorem prime_oneHundredSixtySixFH_5814727 : Nat.Prime 5814727 := by norm_num

private theorem prime_oneHundredSixtySixFH_6476963 : Nat.Prime 6476963 := by norm_num

private theorem prime_oneHundredSixtySixFH_7055159 : Nat.Prime 7055159 := by norm_num

private theorem prime_oneHundredSixtySixFH_7228183 : Nat.Prime 7228183 := by norm_num

private theorem prime_oneHundredSixtySixFH_7353097 : Nat.Prime 7353097 := by norm_num

private theorem prime_oneHundredSixtySixFH_7439623 : Nat.Prime 7439623 := by norm_num

private theorem prime_oneHundredSixtySixFH_7546069 : Nat.Prime 7546069 := by norm_num

private theorem prime_oneHundredSixtySixFH_7687627 : Nat.Prime 7687627 := by norm_num

private theorem prime_oneHundredSixtySixFH_7835909 : Nat.Prime 7835909 := by norm_num

private theorem prime_oneHundredSixtySixFH_8586181 : Nat.Prime 8586181 := by norm_num

private theorem prime_oneHundredSixtySixFH_8639363 : Nat.Prime 8639363 := by norm_num

private theorem prime_oneHundredSixtySixFH_9466021 : Nat.Prime 9466021 := by norm_num

private theorem prime_oneHundredSixtySixFH_9647501 : Nat.Prime 9647501 := by norm_num

private theorem prime_oneHundredSixtySixFH_9785129 : Nat.Prime 9785129 := by norm_num

private theorem prime_oneHundredSixtySixFH_9843979 : Nat.Prime 9843979 := by norm_num

private theorem prime_oneHundredSixtySixFH_10550713 : Nat.Prime 10550713 := by norm_num

private theorem prime_oneHundredSixtySixFH_10704709 : Nat.Prime 10704709 := by norm_num

private theorem prime_oneHundredSixtySixFH_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredSixtySixFH_11486099 : Nat.Prime 11486099 := by norm_num

private theorem prime_oneHundredSixtySixFH_11491033 : Nat.Prime 11491033 := by norm_num

private theorem prime_oneHundredSixtySixFH_11746151 : Nat.Prime 11746151 := by norm_num

private theorem prime_oneHundredSixtySixFH_13902431 : Nat.Prime 13902431 := by norm_num

private theorem prime_oneHundredSixtySixFH_13977427 : Nat.Prime 13977427 := by norm_num

private theorem prime_oneHundredSixtySixFH_14016179 : Nat.Prime 14016179 := by norm_num

private theorem prime_oneHundredSixtySixFH_14577133 : Nat.Prime 14577133 := by norm_num

private theorem prime_oneHundredSixtySixFH_14722607 : Nat.Prime 14722607 := by norm_num

private theorem prime_oneHundredSixtySixFH_14796721 : Nat.Prime 14796721 := by norm_num

private theorem prime_oneHundredSixtySixFH_15742193 : Nat.Prime 15742193 := by norm_num

private theorem prime_oneHundredSixtySixFH_16248593 : Nat.Prime 16248593 := by norm_num

private theorem prime_oneHundredSixtySixFH_17064653 : Nat.Prime 17064653 := by norm_num

private theorem prime_oneHundredSixtySixFH_17540539 : Nat.Prime 17540539 := by norm_num

private theorem prime_oneHundredSixtySixFH_18197411 : Nat.Prime 18197411 := by norm_num

private theorem prime_oneHundredSixtySixFH_19655327 : Nat.Prime 19655327 := by norm_num

private theorem prime_oneHundredSixtySixFH_20037197 : Nat.Prime 20037197 := by norm_num

private theorem prime_oneHundredSixtySixFH_20659799 : Nat.Prime 20659799 := by norm_num

private theorem prime_oneHundredSixtySixFH_21107227 : Nat.Prime 21107227 := by norm_num

private theorem prime_oneHundredSixtySixFH_21468827 : Nat.Prime 21468827 := by norm_num

private theorem prime_oneHundredSixtySixFH_21937477 : Nat.Prime 21937477 := by norm_num

private theorem prime_oneHundredSixtySixFH_22096429 : Nat.Prime 22096429 := by norm_num

private theorem prime_oneHundredSixtySixFH_22509299 : Nat.Prime 22509299 := by norm_num

private theorem prime_oneHundredSixtySixFH_23188237 : Nat.Prime 23188237 := by norm_num

private theorem prime_oneHundredSixtySixFH_24124427 : Nat.Prime 24124427 := by norm_num

private theorem prime_oneHundredSixtySixFH_24826469 : Nat.Prime 24826469 := by norm_num

private theorem prime_oneHundredSixtySixFH_26057809 : Nat.Prime 26057809 := by norm_num

private theorem prime_oneHundredSixtySixFH_26854979 : Nat.Prime 26854979 := by norm_num

private theorem prime_oneHundredSixtySixFH_28855381 : Nat.Prime 28855381 := by norm_num

private theorem prime_oneHundredSixtySixFH_30750509 : Nat.Prime 30750509 := by
  apply lucas_primality 30750509 (2 : ZMod 30750509)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7687627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7687627, 1)] : List FactorBlock).map factorBlockValue).prod) = 30750509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7687627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 30750509) ^ 15375254 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 30750509) ^ 4 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_34400683 : Nat.Prime 34400683 := by
  apply lucas_primality 34400683 (2 : ZMod 34400683)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1911149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1911149, 1)] : List FactorBlock).map factorBlockValue).prod) = 34400683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_1911149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34400683) ^ 17200341 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 34400683) ^ 11466894 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 34400683) ^ 18 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_34660319 : Nat.Prime 34660319 := by
  apply lucas_primality 34660319 (7 : ZMod 34660319)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (225067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (225067, 1)] : List FactorBlock).map factorBlockValue).prod) = 34660319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_225067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 34660319) ^ 17330159 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 34660319) ^ 4951474 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 34660319) ^ 3150938 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 34660319) ^ 154 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_35586779 : Nat.Prime 35586779 := by
  apply lucas_primality 35586779 (2 : ZMod 35586779)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (183437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (183437, 1)] : List FactorBlock).map factorBlockValue).prod) = 35586779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_97
      · exact prime_oneHundredSixtySixFH_183437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35586779) ^ 17793389 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 35586779) ^ 366874 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 35586779) ^ 194 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_38291287 : Nat.Prime 38291287 := by
  apply lucas_primality 38291287 (5 : ZMod 38291287)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (61, 1), (9511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (61, 1), (9511, 1)] : List FactorBlock).map factorBlockValue).prod) = 38291287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_61
      · exact prime_oneHundredSixtySixFH_9511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38291287) ^ 19145643 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 38291287) ^ 12763762 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 38291287) ^ 3481026 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 38291287) ^ 627726 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 38291287) ^ 4026 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_40066843 : Nat.Prime 40066843 := by
  apply lucas_primality 40066843 (5 : ZMod 40066843)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 2), (3023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 2), (3023, 1)] : List FactorBlock).map factorBlockValue).prod) = 40066843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_47
      · exact prime_oneHundredSixtySixFH_3023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 40066843) ^ 20033421 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 40066843) ^ 13355614 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 40066843) ^ 852486 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 40066843) ^ 13254 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_40683641 : Nat.Prime 40683641 := by
  apply lucas_primality 40683641 (3 : ZMod 40683641)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (307, 1), (3313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (307, 1), (3313, 1)] : List FactorBlock).map factorBlockValue).prod) = 40683641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_307
      · exact prime_oneHundredSixtySixFH_3313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40683641) ^ 20341820 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 40683641) ^ 8136728 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 40683641) ^ 132520 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 40683641) ^ 12280 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_41319599 : Nat.Prime 41319599 := by
  apply lucas_primality 41319599 (17 : ZMod 41319599)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20659799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20659799, 1)] : List FactorBlock).map factorBlockValue).prod) = 41319599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_20659799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 41319599) ^ 20659799 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 41319599) ^ 2 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_43423811 : Nat.Prime 43423811 := by
  apply lucas_primality 43423811 (2 : ZMod 43423811)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (107, 1), (40583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (107, 1), (40583, 1)] : List FactorBlock).map factorBlockValue).prod) = 43423811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_107
      · exact prime_oneHundredSixtySixFH_40583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43423811) ^ 21711905 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43423811) ^ 8684762 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43423811) ^ 405830 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43423811) ^ 1070 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_45181883 : Nat.Prime 45181883 := by
  apply lucas_primality 45181883 (2 : ZMod 45181883)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (353, 1), (63997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (353, 1), (63997, 1)] : List FactorBlock).map factorBlockValue).prod) = 45181883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_353
      · exact prime_oneHundredSixtySixFH_63997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45181883) ^ 22590941 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 45181883) ^ 127994 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 45181883) ^ 706 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_51137599 : Nat.Prime 51137599 := by
  apply lucas_primality 51137599 (6 : ZMod 51137599)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (47, 1), (10667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (47, 1), (10667, 1)] : List FactorBlock).map factorBlockValue).prod) = 51137599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_47
      · exact prime_oneHundredSixtySixFH_10667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 51137599) ^ 25568799 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 51137599) ^ 17045866 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 51137599) ^ 3008094 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 51137599) ^ 1088034 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 51137599) ^ 4794 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_52311409 : Nat.Prime 52311409 := by
  apply lucas_primality 52311409 (7 : ZMod 52311409)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (41, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (41, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) = 52311409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_41
      · exact prime_oneHundredSixtySixFH_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 52311409) ^ 26155704 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 52311409) ^ 17437136 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 52311409) ^ 2753232 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 52311409) ^ 1275888 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 52311409) ^ 37392 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_57096913 : Nat.Prime 57096913 := by
  apply lucas_primality 57096913 (5 : ZMod 57096913)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (107, 1), (11117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (107, 1), (11117, 1)] : List FactorBlock).map factorBlockValue).prod) = 57096913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_107
      · exact prime_oneHundredSixtySixFH_11117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 57096913) ^ 28548456 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 57096913) ^ 19032304 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 57096913) ^ 533616 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 57096913) ^ 5136 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_1811
      · exact prime_oneHundredSixtySixFH_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_64372951 : Nat.Prime 64372951 := by
  apply lucas_primality 64372951 (3 : ZMod 64372951)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (19, 1), (7529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (19, 1), (7529, 1)] : List FactorBlock).map factorBlockValue).prod) = 64372951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_7529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64372951) ^ 32186475 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 64372951) ^ 21457650 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 64372951) ^ 12874590 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 64372951) ^ 3388050 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 64372951) ^ 8550 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_64739617 : Nat.Prime 64739617 := by
  apply lucas_primality 64739617 (11 : ZMod 64739617)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (674371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (674371, 1)] : List FactorBlock).map factorBlockValue).prod) = 64739617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_674371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 64739617) ^ 32369808 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 64739617) ^ 21579872 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 64739617) ^ 96 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_65223539 : Nat.Prime 65223539 := by
  apply lucas_primality 65223539 (2 : ZMod 65223539)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (41, 1), (34583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (41, 1), (34583, 1)] : List FactorBlock).map factorBlockValue).prod) = 65223539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_23
      · exact prime_oneHundredSixtySixFH_41
      · exact prime_oneHundredSixtySixFH_34583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 65223539) ^ 32611769 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 65223539) ^ 2835806 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 65223539) ^ 1590818 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 65223539) ^ 1886 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_68311871 : Nat.Prime 68311871 := by
  apply lucas_primality 68311871 (11 : ZMod 68311871)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (621017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (621017, 1)] : List FactorBlock).map factorBlockValue).prod) = 68311871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_621017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 68311871) ^ 34155935 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 68311871) ^ 13662374 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 68311871) ^ 6210170 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 68311871) ^ 110 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_69320639 : Nat.Prime 69320639 := by
  apply lucas_primality 69320639 (11 : ZMod 69320639)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34660319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34660319, 1)] : List FactorBlock).map factorBlockValue).prod) = 69320639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_34660319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 69320639) ^ 34660319 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 69320639) ^ 2 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_71364169 : Nat.Prime 71364169 := by
  apply lucas_primality 71364169 (11 : ZMod 71364169)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (103, 1), (9623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (103, 1), (9623, 1)] : List FactorBlock).map factorBlockValue).prod) = 71364169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_103
      · exact prime_oneHundredSixtySixFH_9623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 71364169) ^ 35682084 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71364169) ^ 23788056 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71364169) ^ 692856 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71364169) ^ 7416 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_75041671 : Nat.Prime 75041671 := by
  apply lucas_primality 75041671 (11 : ZMod 75041671)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (227399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (227399, 1)] : List FactorBlock).map factorBlockValue).prod) = 75041671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_227399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 75041671) ^ 37520835 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 75041671) ^ 25013890 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 75041671) ^ 15008334 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 75041671) ^ 6821970 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 75041671) ^ 330 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_77743973 : Nat.Prime 77743973 := by
  apply lucas_primality 77743973 (2 : ZMod 77743973)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (677, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (677, 1), (1511, 1)] : List FactorBlock).map factorBlockValue).prod) = 77743973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_677
      · exact prime_oneHundredSixtySixFH_1511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77743973) ^ 38871986 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 77743973) ^ 4091788 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 77743973) ^ 114836 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 77743973) ^ 51452 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_78665099 : Nat.Prime 78665099 := by
  apply lucas_primality 78665099 (2 : ZMod 78665099)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (199, 1), (197651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (199, 1), (197651, 1)] : List FactorBlock).map factorBlockValue).prod) = 78665099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_199
      · exact prime_oneHundredSixtySixFH_197651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 78665099) ^ 39332549 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 78665099) ^ 395302 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 78665099) ^ 398 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_78681523 : Nat.Prime 78681523 := by
  apply lucas_primality 78681523 (2 : ZMod 78681523)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1279, 1), (10253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1279, 1), (10253, 1)] : List FactorBlock).map factorBlockValue).prod) = 78681523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_1279
      · exact prime_oneHundredSixtySixFH_10253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 78681523) ^ 39340761 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 78681523) ^ 26227174 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 78681523) ^ 61518 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 78681523) ^ 7674 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_80037151 : Nat.Prime 80037151 := by
  apply lucas_primality 80037151 (3 : ZMod 80037151)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (533581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (533581, 1)] : List FactorBlock).map factorBlockValue).prod) = 80037151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_533581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 80037151) ^ 40018575 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 80037151) ^ 26679050 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 80037151) ^ 16007430 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 80037151) ^ 150 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_84544753 : Nat.Prime 84544753 := by
  apply lucas_primality 84544753 (7 : ZMod 84544753)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (53, 1), (167, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (53, 1), (167, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) = 84544753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_53
      · exact prime_oneHundredSixtySixFH_167
      · exact prime_oneHundredSixtySixFH_199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 84544753) ^ 42272376 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 84544753) ^ 28181584 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 84544753) ^ 1595184 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 84544753) ^ 506256 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 84544753) ^ 424848 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_95125103 : Nat.Prime 95125103 := by
  apply lucas_primality 95125103 (5 : ZMod 95125103)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (2067937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (2067937, 1)] : List FactorBlock).map factorBlockValue).prod) = 95125103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_23
      · exact prime_oneHundredSixtySixFH_2067937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 95125103) ^ 47562551 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 95125103) ^ 4135874 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 95125103) ^ 46 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_110875733 : Nat.Prime 110875733 := by
  apply lucas_primality 110875733 (3 : ZMod 110875733)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (23, 1), (331, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (23, 1), (331, 2)] : List FactorBlock).map factorBlockValue).prod) = 110875733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_23
      · exact prime_oneHundredSixtySixFH_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 110875733) ^ 55437866 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 110875733) ^ 10079612 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 110875733) ^ 4820684 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 110875733) ^ 334972 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_113895619 : Nat.Prime 113895619 := by
  apply lucas_primality 113895619 (2 : ZMod 113895619)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (907, 1), (20929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (907, 1), (20929, 1)] : List FactorBlock).map factorBlockValue).prod) = 113895619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_907
      · exact prime_oneHundredSixtySixFH_20929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113895619) ^ 56947809 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 113895619) ^ 37965206 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 113895619) ^ 125574 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 113895619) ^ 5442 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_115545581 : Nat.Prime 115545581 := by
  apply lucas_primality 115545581 (2 : ZMod 115545581)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (5777279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (5777279, 1)] : List FactorBlock).map factorBlockValue).prod) = 115545581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_5777279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 115545581) ^ 57772790 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 115545581) ^ 23109116 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 115545581) ^ 20 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_118834103 : Nat.Prime 118834103 := by
  apply lucas_primality 118834103 (5 : ZMod 118834103)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (181, 1), (328271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (181, 1), (328271, 1)] : List FactorBlock).map factorBlockValue).prod) = 118834103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_181
      · exact prime_oneHundredSixtySixFH_328271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 118834103) ^ 59417051 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 118834103) ^ 656542 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 118834103) ^ 362 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_118983077 : Nat.Prime 118983077 := by
  apply lucas_primality 118983077 (2 : ZMod 118983077)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3691, 1), (8059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3691, 1), (8059, 1)] : List FactorBlock).map factorBlockValue).prod) = 118983077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3691
      · exact prime_oneHundredSixtySixFH_8059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 118983077) ^ 59491538 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 118983077) ^ 32236 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 118983077) ^ 14764 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_132355747 : Nat.Prime 132355747 := by
  apply lucas_primality 132355747 (2 : ZMod 132355747)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7353097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7353097, 1)] : List FactorBlock).map factorBlockValue).prod) = 132355747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7353097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 132355747) ^ 66177873 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 132355747) ^ 44118582 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 132355747) ^ 18 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_144074509 : Nat.Prime 144074509 := by
  apply lucas_primality 144074509 (2 : ZMod 144074509)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3461, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3461, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) = 144074509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_3461
      · exact prime_oneHundredSixtySixFH_3469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 144074509) ^ 72037254 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144074509) ^ 48024836 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144074509) ^ 41628 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 144074509) ^ 41532 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_144571087 : Nat.Prime 144571087 := by
  apply lucas_primality 144571087 (3 : ZMod 144571087)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (730157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (730157, 1)] : List FactorBlock).map factorBlockValue).prod) = 144571087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_730157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 144571087) ^ 72285543 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 144571087) ^ 48190362 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 144571087) ^ 13142826 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 144571087) ^ 198 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_154629119 : Nat.Prime 154629119 := by
  apply lucas_primality 154629119 (7 : ZMod 154629119)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43, 1), (397, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43, 1), (397, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 154629119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_43
      · exact prime_oneHundredSixtySixFH_397
      · exact prime_oneHundredSixtySixFH_647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 154629119) ^ 77314559 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 154629119) ^ 22089874 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 154629119) ^ 3596026 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 154629119) ^ 389494 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 154629119) ^ 238994 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_160291889 : Nat.Prime 160291889 := by
  apply lucas_primality 160291889 (3 : ZMod 160291889)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (311, 1), (32213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (311, 1), (32213, 1)] : List FactorBlock).map factorBlockValue).prod) = 160291889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_311
      · exact prime_oneHundredSixtySixFH_32213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 160291889) ^ 80145944 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 160291889) ^ 515408 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 160291889) ^ 4976 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_176140541 : Nat.Prime 176140541 := by
  apply lucas_primality 176140541 (2 : ZMod 176140541)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (503, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (503, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 176140541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_503
      · exact prime_oneHundredSixtySixFH_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 176140541) ^ 88070270 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 176140541) ^ 35228108 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 176140541) ^ 350180 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 176140541) ^ 10060 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_183519169 : Nat.Prime 183519169 := by
  apply lucas_primality 183519169 (26 : ZMod 183519169)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (136547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (136547, 1)] : List FactorBlock).map factorBlockValue).prod) = 183519169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_136547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (26 : ZMod 183519169) ^ 91759584 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (26 : ZMod 183519169) ^ 61173056 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (26 : ZMod 183519169) ^ 26217024 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (26 : ZMod 183519169) ^ 1344 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_186178393 : Nat.Prime 186178393 := by
  apply lucas_primality 186178393 (5 : ZMod 186178393)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (861937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (861937, 1)] : List FactorBlock).map factorBlockValue).prod) = 186178393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_861937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 186178393) ^ 93089196 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 186178393) ^ 62059464 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 186178393) ^ 216 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_190025999 : Nat.Prime 190025999 := by
  apply lucas_primality 190025999 (7 : ZMod 190025999)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (840823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (840823, 1)] : List FactorBlock).map factorBlockValue).prod) = 190025999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_113
      · exact prime_oneHundredSixtySixFH_840823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 190025999) ^ 95012999 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 190025999) ^ 1681646 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 190025999) ^ 226 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_227257843 : Nat.Prime 227257843 := by
  apply lucas_primality 227257843 (2 : ZMod 227257843)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (5410901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (5410901, 1)] : List FactorBlock).map factorBlockValue).prod) = 227257843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_5410901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 227257843) ^ 113628921 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 227257843) ^ 75752614 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 227257843) ^ 32465406 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 227257843) ^ 42 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_232554011 : Nat.Prime 232554011 := by
  apply lucas_primality 232554011 (6 : ZMod 232554011)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (251, 1), (7127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (251, 1), (7127, 1)] : List FactorBlock).map factorBlockValue).prod) = 232554011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_251
      · exact prime_oneHundredSixtySixFH_7127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 232554011) ^ 116277005 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 232554011) ^ 46510802 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 232554011) ^ 17888770 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 232554011) ^ 926510 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 232554011) ^ 32630 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_243315013 : Nat.Prime 243315013 := by
  apply lucas_primality 243315013 (2 : ZMod 243315013)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (347, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (347, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) = 243315013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_71
      · exact prime_oneHundredSixtySixFH_347
      · exact prime_oneHundredSixtySixFH_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 243315013) ^ 121657506 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 243315013) ^ 81105004 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 243315013) ^ 3426972 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 243315013) ^ 701196 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 243315013) ^ 295644 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_269555177 : Nat.Prime 269555177 := by
  apply lucas_primality 269555177 (3 : ZMod 269555177)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (883, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (883, 1), (3469, 1)] : List FactorBlock).map factorBlockValue).prod) = 269555177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_883
      · exact prime_oneHundredSixtySixFH_3469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 269555177) ^ 134777588 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 269555177) ^ 24505016 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 269555177) ^ 305272 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 269555177) ^ 77704 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_275174579 : Nat.Prime 275174579 := by
  apply lucas_primality 275174579 (2 : ZMod 275174579)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19655327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19655327, 1)] : List FactorBlock).map factorBlockValue).prod) = 275174579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_19655327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 275174579) ^ 137587289 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 275174579) ^ 39310654 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 275174579) ^ 14 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_309258239 : Nat.Prime 309258239 := by
  apply lucas_primality 309258239 (11 : ZMod 309258239)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (154629119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (154629119, 1)] : List FactorBlock).map factorBlockValue).prod) = 309258239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_154629119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 309258239) ^ 154629119 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 309258239) ^ 2 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_337254167 : Nat.Prime 337254167 := by
  apply lucas_primality 337254167 (5 : ZMod 337254167)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (5814727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (5814727, 1)] : List FactorBlock).map factorBlockValue).prod) = 337254167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_29
      · exact prime_oneHundredSixtySixFH_5814727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 337254167) ^ 168627083 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 337254167) ^ 11629454 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 337254167) ^ 58 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_348882137 : Nat.Prime 348882137 := by
  apply lucas_primality 348882137 (3 : ZMod 348882137)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (89, 1), (490003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (89, 1), (490003, 1)] : List FactorBlock).map factorBlockValue).prod) = 348882137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_89
      · exact prime_oneHundredSixtySixFH_490003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 348882137) ^ 174441068 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 348882137) ^ 3920024 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 348882137) ^ 712 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_349851193 : Nat.Prime 349851193 := by
  apply lucas_primality 349851193 (7 : ZMod 349851193)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (14577133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (14577133, 1)] : List FactorBlock).map factorBlockValue).prod) = 349851193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_14577133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 349851193) ^ 174925596 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 349851193) ^ 116617064 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 349851193) ^ 24 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_355242331 : Nat.Prime 355242331 := by
  apply lucas_primality 355242331 (2 : ZMod 355242331)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (31, 1), (157, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (31, 1), (157, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 355242331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_31
      · exact prime_oneHundredSixtySixFH_157
      · exact prime_oneHundredSixtySixFH_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 355242331) ^ 177621165 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 355242331) ^ 118414110 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 355242331) ^ 71048466 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 355242331) ^ 11459430 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 355242331) ^ 2262690 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 355242331) ^ 438030 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_376654387 : Nat.Prime 376654387 := by
  apply lucas_primality 376654387 (2 : ZMod 376654387)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (421, 1), (149111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (421, 1), (149111, 1)] : List FactorBlock).map factorBlockValue).prod) = 376654387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_421
      · exact prime_oneHundredSixtySixFH_149111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 376654387) ^ 188327193 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 376654387) ^ 125551462 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 376654387) ^ 894666 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 376654387) ^ 2526 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_546494969 : Nat.Prime 546494969 := by
  apply lucas_primality 546494969 (3 : ZMod 546494969)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (68311871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (68311871, 1)] : List FactorBlock).map factorBlockValue).prod) = 546494969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_68311871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 546494969) ^ 273247484 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 546494969) ^ 8 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_550349159 : Nat.Prime 550349159 := by
  apply lucas_primality 550349159 (19 : ZMod 550349159)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (275174579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (275174579, 1)] : List FactorBlock).map factorBlockValue).prod) = 550349159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_275174579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (19 : ZMod 550349159) ^ 275174579 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (19 : ZMod 550349159) ^ 2 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_564566767 : Nat.Prime 564566767 := by
  apply lucas_primality 564566767 (3 : ZMod 564566767)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1871, 1), (50291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1871, 1), (50291, 1)] : List FactorBlock).map factorBlockValue).prod) = 564566767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_1871
      · exact prime_oneHundredSixtySixFH_50291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 564566767) ^ 282283383 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 564566767) ^ 188188922 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 564566767) ^ 301746 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 564566767) ^ 11226 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_656030069 : Nat.Prime 656030069 := by
  apply lucas_primality 656030069 (2 : ZMod 656030069)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (9647501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (9647501, 1)] : List FactorBlock).map factorBlockValue).prod) = 656030069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_9647501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 656030069) ^ 328015034 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 656030069) ^ 38590004 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 656030069) ^ 68 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_17203
      · exact prime_oneHundredSixtySixFH_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_810849569 : Nat.Prime 810849569 := by
  apply lucas_primality 810849569 (3 : ZMod 810849569)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3881, 1), (6529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3881, 1), (6529, 1)] : List FactorBlock).map factorBlockValue).prod) = 810849569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3881
      · exact prime_oneHundredSixtySixFH_6529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 810849569) ^ 405424784 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 810849569) ^ 208928 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 810849569) ^ 124192 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_827354377 : Nat.Prime 827354377 := by
  apply lucas_primality 827354377 (10 : ZMod 827354377)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11491033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11491033, 1)] : List FactorBlock).map factorBlockValue).prod) = 827354377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11491033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 827354377) ^ 413677188 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 827354377) ^ 275784792 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 827354377) ^ 72 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_855521309 : Nat.Prime 855521309 := by
  apply lucas_primality 855521309 (2 : ZMod 855521309)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (523, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (523, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 855521309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_101
      · exact prime_oneHundredSixtySixFH_523
      · exact prime_oneHundredSixtySixFH_4049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 855521309) ^ 427760654 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 855521309) ^ 8470508 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 855521309) ^ 1635796 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 855521309) ^ 211292 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_859672139 : Nat.Prime 859672139 := by
  apply lucas_primality 859672139 (6 : ZMod 859672139)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (433, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (433, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) = 859672139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_433
      · exact prime_oneHundredSixtySixFH_4019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 859672139) ^ 429836069 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 859672139) ^ 66128626 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 859672139) ^ 45245902 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 859672139) ^ 1985386 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 859672139) ^ 213902 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1216210487 : Nat.Prime 1216210487 := by
  apply lucas_primality 1216210487 (5 : ZMod 1216210487)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2039, 1), (298237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2039, 1), (298237, 1)] : List FactorBlock).map factorBlockValue).prod) = 1216210487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_2039
      · exact prime_oneHundredSixtySixFH_298237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1216210487) ^ 608105243 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1216210487) ^ 596474 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1216210487) ^ 4078 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1248407033 : Nat.Prime 1248407033 := by
  apply lucas_primality 1248407033 (3 : ZMod 1248407033)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (3806119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (3806119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1248407033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_41
      · exact prime_oneHundredSixtySixFH_3806119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1248407033) ^ 624203516 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1248407033) ^ 30448952 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1248407033) ^ 328 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1259042483 : Nat.Prime 1259042483 := by
  apply lucas_primality 1259042483 (2 : ZMod 1259042483)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (1217, 1), (17837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (1217, 1), (17837, 1)] : List FactorBlock).map factorBlockValue).prod) = 1259042483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_29
      · exact prime_oneHundredSixtySixFH_1217
      · exact prime_oneHundredSixtySixFH_17837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1259042483) ^ 629521241 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259042483) ^ 43415258 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259042483) ^ 1034546 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1259042483) ^ 70586 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1464611077 : Nat.Prime 1464611077 := by
  apply lucas_primality 1464611077 (2 : ZMod 1464611077)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (40683641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (40683641, 1)] : List FactorBlock).map factorBlockValue).prod) = 1464611077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_40683641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1464611077) ^ 732305538 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1464611077) ^ 488203692 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1464611077) ^ 36 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1472041729 : Nat.Prime 1472041729 := by
  apply lucas_primality 1472041729 (13 : ZMod 1472041729)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (212969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (212969, 1)] : List FactorBlock).map factorBlockValue).prod) = 1472041729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_212969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 1472041729) ^ 736020864 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 1472041729) ^ 490680576 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 1472041729) ^ 6912 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1560773969 : Nat.Prime 1560773969 := by
  apply lucas_primality 1560773969 (3 : ZMod 1560773969)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (29, 1), (353, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (29, 1), (353, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1560773969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_29
      · exact prime_oneHundredSixtySixFH_353
      · exact prime_oneHundredSixtySixFH_733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1560773969) ^ 780386984 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1560773969) ^ 120059536 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1560773969) ^ 53819792 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1560773969) ^ 4421456 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1560773969) ^ 2129296 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1663695337 : Nat.Prime 1663695337 := by
  apply lucas_primality 1663695337 (5 : ZMod 1663695337)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (69320639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (69320639, 1)] : List FactorBlock).map factorBlockValue).prod) = 1663695337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_69320639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1663695337) ^ 831847668 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663695337) ^ 554565112 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1663695337) ^ 24 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1691877721 : Nat.Prime 1691877721 := by
  apply lucas_primality 1691877721 (11 : ZMod 1691877721)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (173, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (173, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1691877721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_173
      · exact prime_oneHundredSixtySixFH_6269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1691877721) ^ 845938860 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1691877721) ^ 563959240 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1691877721) ^ 338375544 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1691877721) ^ 130144440 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1691877721) ^ 9779640 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1691877721) ^ 269880 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1694428427 : Nat.Prime 1694428427 := by
  apply lucas_primality 1694428427 (2 : ZMod 1694428427)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (5073139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (5073139, 1)] : List FactorBlock).map factorBlockValue).prod) = 1694428427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_167
      · exact prime_oneHundredSixtySixFH_5073139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1694428427) ^ 847214213 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1694428427) ^ 10146278 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1694428427) ^ 334 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1801284427 : Nat.Prime 1801284427 := by
  apply lucas_primality 1801284427 (3 : ZMod 1801284427)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (83, 1), (271, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (83, 1), (271, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) = 1801284427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_83
      · exact prime_oneHundredSixtySixFH_271
      · exact prime_oneHundredSixtySixFH_1483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1801284427) ^ 900642213 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1801284427) ^ 600428142 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1801284427) ^ 21702222 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1801284427) ^ 6646806 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1801284427) ^ 1214622 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1866992089 : Nat.Prime 1866992089 := by
  apply lucas_primality 1866992089 (11 : ZMod 1866992089)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (17, 1), (131, 1), (2687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (17, 1), (131, 1), (2687, 1)] : List FactorBlock).map factorBlockValue).prod) = 1866992089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_131
      · exact prime_oneHundredSixtySixFH_2687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1866992089) ^ 933496044 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1866992089) ^ 622330696 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1866992089) ^ 143614776 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1866992089) ^ 109823064 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1866992089) ^ 14251848 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 1866992089) ^ 694824 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_2136063263 : Nat.Prime 2136063263 := by
  apply lucas_primality 2136063263 (5 : ZMod 2136063263)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (827, 1), (1291453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (827, 1), (1291453, 1)] : List FactorBlock).map factorBlockValue).prod) = 2136063263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_827
      · exact prime_oneHundredSixtySixFH_1291453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2136063263) ^ 1068031631 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2136063263) ^ 2582906 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2136063263) ^ 1654 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_2770116577 : Nat.Prime 2770116577 := by
  apply lucas_primality 2770116577 (5 : ZMod 2770116577)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (28855381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (28855381, 1)] : List FactorBlock).map factorBlockValue).prod) = 2770116577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_28855381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2770116577) ^ 1385058288 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2770116577) ^ 923372192 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2770116577) ^ 96 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_3000898489 : Nat.Prime 3000898489 := by
  apply lucas_primality 3000898489 (11 : ZMod 3000898489)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (47, 1), (389, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (47, 1), (389, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 3000898489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_47
      · exact prime_oneHundredSixtySixFH_389
      · exact prime_oneHundredSixtySixFH_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3000898489) ^ 1500449244 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3000898489) ^ 1000299496 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3000898489) ^ 428699784 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3000898489) ^ 63848904 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3000898489) ^ 7714392 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3000898489) ^ 3071544 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_3006331301 : Nat.Prime 3006331301 := by
  apply lucas_primality 3006331301 (2 : ZMod 3006331301)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 2), (127, 1), (4831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 2), (127, 1), (4831, 1)] : List FactorBlock).map factorBlockValue).prod) = 3006331301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_127
      · exact prime_oneHundredSixtySixFH_4831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3006331301) ^ 1503165650 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3006331301) ^ 601266260 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3006331301) ^ 429475900 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3006331301) ^ 23671900 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3006331301) ^ 622300 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_3303345043 : Nat.Prime 3303345043 := by
  apply lucas_primality 3303345043 (2 : ZMod 3303345043)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (183519169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (183519169, 1)] : List FactorBlock).map factorBlockValue).prod) = 3303345043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_183519169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3303345043) ^ 1651672521 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3303345043) ^ 1101115014 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3303345043) ^ 18 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_3364882237 : Nat.Prime 3364882237 := by
  apply lucas_primality 3364882237 (2 : ZMod 3364882237)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (373, 1), (9281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (373, 1), (9281, 1)] : List FactorBlock).map factorBlockValue).prod) = 3364882237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_373
      · exact prime_oneHundredSixtySixFH_9281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3364882237) ^ 1682441118 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3364882237) ^ 1121627412 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3364882237) ^ 9021132 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3364882237) ^ 362556 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_4031659717 : Nat.Prime 4031659717 := by
  apply lucas_primality 4031659717 (2 : ZMod 4031659717)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (443, 1), (108343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (443, 1), (108343, 1)] : List FactorBlock).map factorBlockValue).prod) = 4031659717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_443
      · exact prime_oneHundredSixtySixFH_108343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4031659717) ^ 2015829858 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4031659717) ^ 1343886572 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4031659717) ^ 575951388 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4031659717) ^ 9100812 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4031659717) ^ 37212 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_4272126527 : Nat.Prime 4272126527 := by
  apply lucas_primality 4272126527 (5 : ZMod 4272126527)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2136063263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2136063263, 1)] : List FactorBlock).map factorBlockValue).prod) = 4272126527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_2136063263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4272126527) ^ 2136063263 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 4272126527) ^ 2 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_4484439161 : Nat.Prime 4484439161 := by
  apply lucas_primality 4484439161 (3 : ZMod 4484439161)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (131, 1), (233, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (131, 1), (233, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) = 4484439161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_131
      · exact prime_oneHundredSixtySixFH_233
      · exact prime_oneHundredSixtySixFH_3673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4484439161) ^ 2242219580 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4484439161) ^ 896887832 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4484439161) ^ 34232360 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4484439161) ^ 19246520 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4484439161) ^ 1220920 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_5929508159 : Nat.Prime 5929508159 := by
  apply lucas_primality 5929508159 (7 : ZMod 5929508159)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (719, 1), (589063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (719, 1), (589063, 1)] : List FactorBlock).map factorBlockValue).prod) = 5929508159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_719
      · exact prime_oneHundredSixtySixFH_589063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5929508159) ^ 2964754079 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 5929508159) ^ 847072594 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 5929508159) ^ 8246882 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 5929508159) ^ 10066 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_31
      · exact prime_oneHundredSixtySixFH_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_6339654679 : Nat.Prime 6339654679 := by
  apply lucas_primality 6339654679 (13 : ZMod 6339654679)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (53, 1), (98207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (53, 1), (98207, 1)] : List FactorBlock).map factorBlockValue).prod) = 6339654679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_29
      · exact prime_oneHundredSixtySixFH_53
      · exact prime_oneHundredSixtySixFH_98207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 6339654679) ^ 3169827339 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 6339654679) ^ 2113218226 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 6339654679) ^ 905664954 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 6339654679) ^ 218608782 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 6339654679) ^ 119616126 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 6339654679) ^ 64554 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_6557939629 : Nat.Prime 6557939629 := by
  apply lucas_primality 6557939629 (6 : ZMod 6557939629)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (546494969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (546494969, 1)] : List FactorBlock).map factorBlockValue).prod) = 6557939629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_546494969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 6557939629) ^ 3278969814 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 6557939629) ^ 2185979876 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 6557939629) ^ 12 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_7107596599 : Nat.Prime 7107596599 := by
  apply lucas_primality 7107596599 (15 : ZMod 7107596599)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3943, 1), (300431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3943, 1), (300431, 1)] : List FactorBlock).map factorBlockValue).prod) = 7107596599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_3943
      · exact prime_oneHundredSixtySixFH_300431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 7107596599) ^ 3553798299 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (15 : ZMod 7107596599) ^ 2369198866 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (15 : ZMod 7107596599) ^ 1802586 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (15 : ZMod 7107596599) ^ 23658 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_8600170751 : Nat.Prime 8600170751 := by
  apply lucas_primality 8600170751 (7 : ZMod 8600170751)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (34400683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (34400683, 1)] : List FactorBlock).map factorBlockValue).prod) = 8600170751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_34400683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 8600170751) ^ 4300085375 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 8600170751) ^ 1720034150 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 8600170751) ^ 250 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_8961440177 : Nat.Prime 8961440177 := by
  apply lucas_primality 8961440177 (3 : ZMod 8961440177)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (269, 1), (160163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (269, 1), (160163, 1)] : List FactorBlock).map factorBlockValue).prod) = 8961440177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_269
      · exact prime_oneHundredSixtySixFH_160163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8961440177) ^ 4480720088 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8961440177) ^ 689341552 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8961440177) ^ 33313904 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8961440177) ^ 55952 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_9439811881 : Nat.Prime 9439811881 := by
  apply lucas_primality 9439811881 (13 : ZMod 9439811881)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (78665099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (78665099, 1)] : List FactorBlock).map factorBlockValue).prod) = 9439811881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_78665099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 9439811881) ^ 4719905940 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 9439811881) ^ 3146603960 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 9439811881) ^ 1887962376 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 9439811881) ^ 120 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_9585629323 : Nat.Prime 9585629323 := by
  apply lucas_primality 9585629323 (2 : ZMod 9585629323)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (499, 1), (617, 1), (5189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (499, 1), (617, 1), (5189, 1)] : List FactorBlock).map factorBlockValue).prod) = 9585629323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_499
      · exact prime_oneHundredSixtySixFH_617
      · exact prime_oneHundredSixtySixFH_5189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9585629323) ^ 4792814661 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9585629323) ^ 3195209774 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9585629323) ^ 19209678 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9585629323) ^ 15535866 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9585629323) ^ 1847298 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_9615690257 : Nat.Prime 9615690257 := by
  apply lucas_primality 9615690257 (3 : ZMod 9615690257)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (887, 1), (677543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (887, 1), (677543, 1)] : List FactorBlock).map factorBlockValue).prod) = 9615690257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_887
      · exact prime_oneHundredSixtySixFH_677543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9615690257) ^ 4807845128 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9615690257) ^ 10840688 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9615690257) ^ 14192 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_9760590451 : Nat.Prime 9760590451 := by
  apply lucas_primality 9760590451 (2 : ZMod 9760590451)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (13, 1), (556159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (13, 1), (556159, 1)] : List FactorBlock).map factorBlockValue).prod) = 9760590451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_556159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9760590451) ^ 4880295225 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9760590451) ^ 3253530150 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9760590451) ^ 1952118090 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9760590451) ^ 750814650 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9760590451) ^ 17550 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_10162286681 : Nat.Prime 10162286681 := by
  apply lucas_primality 10162286681 (3 : ZMod 10162286681)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (13, 1), (2791837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (13, 1), (2791837, 1)] : List FactorBlock).map factorBlockValue).prod) = 10162286681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_2791837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10162286681) ^ 5081143340 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10162286681) ^ 2032457336 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10162286681) ^ 1451755240 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10162286681) ^ 781714360 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10162286681) ^ 3640 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_11158130381 : Nat.Prime 11158130381 := by
  apply lucas_primality 11158130381 (2 : ZMod 11158130381)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (587, 1), (50023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (587, 1), (50023, 1)] : List FactorBlock).map factorBlockValue).prod) = 11158130381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_587
      · exact prime_oneHundredSixtySixFH_50023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11158130381) ^ 5579065190 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11158130381) ^ 2231626076 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11158130381) ^ 587270020 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11158130381) ^ 19008740 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11158130381) ^ 223060 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_11808541243 : Nat.Prime 11808541243 := by
  apply lucas_primality 11808541243 (11 : ZMod 11808541243)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (656030069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (656030069, 1)] : List FactorBlock).map factorBlockValue).prod) = 11808541243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_656030069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 11808541243) ^ 5904270621 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 11808541243) ^ 3936180414 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 11808541243) ^ 18 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_15297925157 : Nat.Prime 15297925157 := by
  apply lucas_primality 15297925157 (2 : ZMod 15297925157)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4231, 1), (903919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4231, 1), (903919, 1)] : List FactorBlock).map factorBlockValue).prod) = 15297925157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_4231
      · exact prime_oneHundredSixtySixFH_903919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15297925157) ^ 7648962578 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15297925157) ^ 3615676 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15297925157) ^ 16924 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_15708605123 : Nat.Prime 15708605123 := by
  apply lucas_primality 15708605123 (5 : ZMod 15708605123)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (160291889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (160291889, 1)] : List FactorBlock).map factorBlockValue).prod) = 15708605123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_160291889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15708605123) ^ 7854302561 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 15708605123) ^ 2244086446 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 15708605123) ^ 98 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_17606579687 : Nat.Prime 17606579687 := by
  apply lucas_primality 17606579687 (5 : ZMod 17606579687)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (109, 1), (4750831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (109, 1), (4750831, 1)] : List FactorBlock).map factorBlockValue).prod) = 17606579687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_109
      · exact prime_oneHundredSixtySixFH_4750831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17606579687) ^ 8803289843 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 17606579687) ^ 1035681158 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 17606579687) ^ 161528254 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 17606579687) ^ 3706 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_18000381593 : Nat.Prime 18000381593 := by
  apply lucas_primality 18000381593 (3 : ZMod 18000381593)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (132355747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (132355747, 1)] : List FactorBlock).map factorBlockValue).prod) = 18000381593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_132355747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 18000381593) ^ 9000190796 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 18000381593) ^ 1058845976 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 18000381593) ^ 136 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_21548394041 : Nat.Prime 21548394041 := by
  apply lucas_primality 21548394041 (3 : ZMod 21548394041)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (73, 1), (409, 1), (18043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (73, 1), (409, 1), (18043, 1)] : List FactorBlock).map factorBlockValue).prod) = 21548394041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_73
      · exact prime_oneHundredSixtySixFH_409
      · exact prime_oneHundredSixtySixFH_18043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21548394041) ^ 10774197020 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 21548394041) ^ 4309678808 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 21548394041) ^ 295183480 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 21548394041) ^ 52685560 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 21548394041) ^ 1194280 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_26121592171 : Nat.Prime 26121592171 := by
  apply lucas_primality 26121592171 (2 : ZMod 26121592171)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (67, 1), (4331939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (67, 1), (4331939, 1)] : List FactorBlock).map factorBlockValue).prod) = 26121592171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_67
      · exact prime_oneHundredSixtySixFH_4331939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26121592171) ^ 13060796085 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26121592171) ^ 8707197390 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26121592171) ^ 5224318434 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26121592171) ^ 389874510 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26121592171) ^ 6030 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_26778232801 : Nat.Prime 26778232801 := by
  apply lucas_primality 26778232801 (7 : ZMod 26778232801)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (11, 1), (43, 1), (2621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (11, 1), (43, 1), (2621, 1)] : List FactorBlock).map factorBlockValue).prod) = 26778232801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_43
      · exact prime_oneHundredSixtySixFH_2621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 26778232801) ^ 13389116400 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 26778232801) ^ 8926077600 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 26778232801) ^ 5355646560 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 26778232801) ^ 2434384800 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 26778232801) ^ 622749600 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 26778232801) ^ 10216800 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_31276175093 : Nat.Prime 31276175093 := by
  apply lucas_primality 31276175093 (2 : ZMod 31276175093)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1051, 1), (7439623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1051, 1), (7439623, 1)] : List FactorBlock).map factorBlockValue).prod) = 31276175093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_1051
      · exact prime_oneHundredSixtySixFH_7439623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31276175093) ^ 15638087546 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 31276175093) ^ 29758492 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 31276175093) ^ 4204 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_31803155147 : Nat.Prime 31803155147 := by
  apply lucas_primality 31803155147 (2 : ZMod 31803155147)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29429, 1), (77191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29429, 1), (77191, 1)] : List FactorBlock).map factorBlockValue).prod) = 31803155147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_29429
      · exact prime_oneHundredSixtySixFH_77191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31803155147) ^ 15901577573 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 31803155147) ^ 4543307878 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 31803155147) ^ 1080674 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 31803155147) ^ 412006 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_33262719901 : Nat.Prime 33262719901 := by
  apply lucas_primality 33262719901 (6 : ZMod 33262719901)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (110875733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (110875733, 1)] : List FactorBlock).map factorBlockValue).prod) = 33262719901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_110875733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 33262719901) ^ 16631359950 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 33262719901) ^ 11087573300 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 33262719901) ^ 6652543980 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 33262719901) ^ 300 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_36219929951 : Nat.Prime 36219929951 := by
  apply lucas_primality 36219929951 (7 : ZMod 36219929951)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (6653, 1), (108883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (6653, 1), (108883, 1)] : List FactorBlock).map factorBlockValue).prod) = 36219929951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_6653
      · exact prime_oneHundredSixtySixFH_108883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 36219929951) ^ 18109964975 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 36219929951) ^ 7243985990 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 36219929951) ^ 5444150 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 36219929951) ^ 332650 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_44542537229 : Nat.Prime 44542537229 := by
  apply lucas_primality 44542537229 (2 : ZMod 44542537229)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (227257843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (227257843, 1)] : List FactorBlock).map factorBlockValue).prod) = 44542537229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_227257843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44542537229) ^ 22271268614 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44542537229) ^ 6363219604 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44542537229) ^ 196 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_63160668199 : Nat.Prime 63160668199 := by
  apply lucas_primality 63160668199 (3 : ZMod 63160668199)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (149, 1), (167, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (149, 1), (167, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) = 63160668199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_83
      · exact prime_oneHundredSixtySixFH_149
      · exact prime_oneHundredSixtySixFH_167
      · exact prime_oneHundredSixtySixFH_1699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 63160668199) ^ 31580334099 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 63160668199) ^ 21053556066 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 63160668199) ^ 760971906 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 63160668199) ^ 423897102 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 63160668199) ^ 378207594 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 63160668199) ^ 37175202 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_77213313937 : Nat.Prime 77213313937 := by
  apply lucas_primality 77213313937 (5 : ZMod 77213313937)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (11, 1), (16248593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (11, 1), (16248593, 1)] : List FactorBlock).map factorBlockValue).prod) = 77213313937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_16248593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 77213313937) ^ 38606656968 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 77213313937) ^ 25737771312 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 77213313937) ^ 7019392176 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 77213313937) ^ 4752 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_82269768761 : Nat.Prime 82269768761 := by
  apply lucas_primality 82269768761 (3 : ZMod 82269768761)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (139, 1), (14796721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (139, 1), (14796721, 1)] : List FactorBlock).map factorBlockValue).prod) = 82269768761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_139
      · exact prime_oneHundredSixtySixFH_14796721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 82269768761) ^ 41134884380 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 82269768761) ^ 16453953752 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 82269768761) ^ 591868840 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 82269768761) ^ 5560 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_85291159189 : Nat.Prime 85291159189 := by
  apply lucas_primality 85291159189 (2 : ZMod 85291159189)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7107596599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7107596599, 1)] : List FactorBlock).map factorBlockValue).prod) = 85291159189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7107596599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 85291159189) ^ 42645579594 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 85291159189) ^ 28430386396 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 85291159189) ^ 12 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_94896739697 : Nat.Prime 94896739697 := by
  apply lucas_primality 94896739697 (3 : ZMod 94896739697)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 2), (47, 1), (269, 1), (3877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 2), (47, 1), (269, 1), (3877, 1)] : List FactorBlock).map factorBlockValue).prod) = 94896739697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_47
      · exact prime_oneHundredSixtySixFH_269
      · exact prime_oneHundredSixtySixFH_3877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 94896739697) ^ 47448369848 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 94896739697) ^ 8626976336 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 94896739697) ^ 2019079568 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 94896739697) ^ 352775984 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 94896739697) ^ 24476848 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_108227926837 : Nat.Prime 108227926837 := by
  apply lucas_primality 108227926837 (2 : ZMod 108227926837)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (3006331301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (3006331301, 1)] : List FactorBlock).map factorBlockValue).prod) = 108227926837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_3006331301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 108227926837) ^ 54113963418 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108227926837) ^ 36075975612 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108227926837) ^ 36 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_117444940969 : Nat.Prime 117444940969 := by
  apply lucas_primality 117444940969 (7 : ZMod 117444940969)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (293, 1), (2389, 1), (6991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (293, 1), (2389, 1), (6991, 1)] : List FactorBlock).map factorBlockValue).prod) = 117444940969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_293
      · exact prime_oneHundredSixtySixFH_2389
      · exact prime_oneHundredSixtySixFH_6991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 117444940969) ^ 58722470484 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 117444940969) ^ 39148313656 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 117444940969) ^ 400835976 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 117444940969) ^ 49160712 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 117444940969) ^ 16799448 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_127563851111 : Nat.Prime 127563851111 := by
  apply lucas_primality 127563851111 (13 : ZMod 127563851111)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (701, 1), (18197411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (701, 1), (18197411, 1)] : List FactorBlock).map factorBlockValue).prod) = 127563851111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_701
      · exact prime_oneHundredSixtySixFH_18197411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 127563851111) ^ 63781925555 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 127563851111) ^ 25512770222 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 127563851111) ^ 181974110 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 127563851111) ^ 7010 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_127859938819 : Nat.Prime 127859938819 := by
  apply lucas_primality 127859938819 (2 : ZMod 127859938819)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (919, 1), (23188237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (919, 1), (23188237, 1)] : List FactorBlock).map factorBlockValue).prod) = 127859938819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_919
      · exact prime_oneHundredSixtySixFH_23188237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 127859938819) ^ 63929969409 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 127859938819) ^ 42619979606 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 127859938819) ^ 139129422 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 127859938819) ^ 5514 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_128771507437 : Nat.Prime 128771507437 := by
  apply lucas_primality 128771507437 (6 : ZMod 128771507437)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (75041671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (75041671, 1)] : List FactorBlock).map factorBlockValue).prod) = 128771507437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_75041671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 128771507437) ^ 64385753718 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 128771507437) ^ 42923835812 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 128771507437) ^ 11706500676 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 128771507437) ^ 9905500572 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 128771507437) ^ 1716 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_133378175431 : Nat.Prime 133378175431 := by
  apply lucas_primality 133378175431 (19 : ZMod 133378175431)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 2), (41, 1), (223, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 2), (41, 1), (223, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 133378175431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_41
      · exact prime_oneHundredSixtySixFH_223
      · exact prime_oneHundredSixtySixFH_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 133378175431) ^ 66689087715 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (19 : ZMod 133378175431) ^ 44459391810 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (19 : ZMod 133378175431) ^ 26675635086 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (19 : ZMod 133378175431) ^ 7019903970 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (19 : ZMod 133378175431) ^ 3253126230 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (19 : ZMod 133378175431) ^ 598108410 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (19 : ZMod 133378175431) ^ 297056070 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_148106475317 : Nat.Prime 148106475317 := by
  apply lucas_primality 148106475317 (2 : ZMod 148106475317)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (25147, 1), (47497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (25147, 1), (47497, 1)] : List FactorBlock).map factorBlockValue).prod) = 148106475317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_31
      · exact prime_oneHundredSixtySixFH_25147
      · exact prime_oneHundredSixtySixFH_47497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 148106475317) ^ 74053237658 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 148106475317) ^ 4777628236 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 148106475317) ^ 5889628 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 148106475317) ^ 3118228 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_179770612753 : Nat.Prime 179770612753 := by
  apply lucas_primality 179770612753 (5 : ZMod 179770612753)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (1248407033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (1248407033, 1)] : List FactorBlock).map factorBlockValue).prod) = 179770612753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_1248407033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 179770612753) ^ 89885306376 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 179770612753) ^ 59923537584 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 179770612753) ^ 144 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_205629864287 : Nat.Prime 205629864287 := by
  apply lucas_primality 205629864287 (5 : ZMod 205629864287)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (23, 1), (353, 1), (14951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (23, 1), (353, 1), (14951, 1)] : List FactorBlock).map factorBlockValue).prod) = 205629864287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_23
      · exact prime_oneHundredSixtySixFH_353
      · exact prime_oneHundredSixtySixFH_14951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 205629864287) ^ 102814932143 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 205629864287) ^ 29375694898 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 205629864287) ^ 18693624026 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 205629864287) ^ 8940428882 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 205629864287) ^ 582520862 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 205629864287) ^ 13753586 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_252303645673 : Nat.Prime 252303645673 := by
  apply lucas_primality 252303645673 (11 : ZMod 252303645673)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (269555177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (269555177, 1)] : List FactorBlock).map factorBlockValue).prod) = 252303645673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_269555177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 252303645673) ^ 126151822836 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 252303645673) ^ 84101215224 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 252303645673) ^ 19407972744 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 252303645673) ^ 936 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_261013968613 : Nat.Prime 261013968613 := by
  apply lucas_primality 261013968613 (2 : ZMod 261013968613)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (61643, 1), (117619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (61643, 1), (117619, 1)] : List FactorBlock).map factorBlockValue).prod) = 261013968613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_61643
      · exact prime_oneHundredSixtySixFH_117619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 261013968613) ^ 130506984306 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 261013968613) ^ 87004656204 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 261013968613) ^ 4234284 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 261013968613) ^ 2219148 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_271539554509 : Nat.Prime 271539554509 := by
  apply lucas_primality 271539554509 (6 : ZMod 271539554509)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (31, 1), (243315013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (31, 1), (243315013, 1)] : List FactorBlock).map factorBlockValue).prod) = 271539554509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_31
      · exact prime_oneHundredSixtySixFH_243315013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 271539554509) ^ 135769777254 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 271539554509) ^ 90513184836 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 271539554509) ^ 8759340468 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 271539554509) ^ 1116 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_272291690273 : Nat.Prime 272291690273 := by
  apply lucas_primality 272291690273 (3 : ZMod 272291690273)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (31, 1), (937, 1), (41849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (31, 1), (937, 1), (41849, 1)] : List FactorBlock).map factorBlockValue).prod) = 272291690273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_31
      · exact prime_oneHundredSixtySixFH_937
      · exact prime_oneHundredSixtySixFH_41849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 272291690273) ^ 136145845136 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 272291690273) ^ 38898812896 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 272291690273) ^ 8783602912 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 272291690273) ^ 290599456 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 272291690273) ^ 6506528 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_296137769987 : Nat.Prime 296137769987 := by
  apply lucas_primality 296137769987 (2 : ZMod 296137769987)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (1663695337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (1663695337, 1)] : List FactorBlock).map factorBlockValue).prod) = 296137769987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_89
      · exact prime_oneHundredSixtySixFH_1663695337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 296137769987) ^ 148068884993 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 296137769987) ^ 3327390674 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 296137769987) ^ 178 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_343170375571 : Nat.Prime 343170375571 := by
  apply lucas_primality 343170375571 (17 : ZMod 343170375571)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (11, 1), (115545581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (11, 1), (115545581, 1)] : List FactorBlock).map factorBlockValue).prod) = 343170375571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_115545581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 343170375571) ^ 171585187785 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 343170375571) ^ 114390125190 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 343170375571) ^ 68634075114 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 343170375571) ^ 31197306870 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 343170375571) ^ 2970 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_355294321411 : Nat.Prime 355294321411 := by
  apply lucas_primality 355294321411 (2 : ZMod 355294321411)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1691877721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1691877721, 1)] : List FactorBlock).map factorBlockValue).prod) = 355294321411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_1691877721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 355294321411) ^ 177647160705 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 355294321411) ^ 118431440470 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 355294321411) ^ 71058864282 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 355294321411) ^ 50756331630 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 355294321411) ^ 210 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_389500600367 : Nat.Prime 389500600367 := by
  apply lucas_primality 389500600367 (5 : ZMod 389500600367)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (311, 1), (3779, 1), (165707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (311, 1), (3779, 1), (165707, 1)] : List FactorBlock).map factorBlockValue).prod) = 389500600367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_311
      · exact prime_oneHundredSixtySixFH_3779
      · exact prime_oneHundredSixtySixFH_165707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 389500600367) ^ 194750300183 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 389500600367) ^ 1252413506 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 389500600367) ^ 103069754 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 389500600367) ^ 2350538 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_391454631943 : Nat.Prime 391454631943 := by
  apply lucas_primality 391454631943 (5 : ZMod 391454631943)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (281, 1), (21107227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (281, 1), (21107227, 1)] : List FactorBlock).map factorBlockValue).prod) = 391454631943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_281
      · exact prime_oneHundredSixtySixFH_21107227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 391454631943) ^ 195727315971 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 391454631943) ^ 130484877314 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 391454631943) ^ 35586784722 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 391454631943) ^ 1393076982 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 391454631943) ^ 18546 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_414550448467 : Nat.Prime 414550448467 := by
  apply lucas_primality 414550448467 (11 : ZMod 414550448467)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (11, 1), (17, 1), (23, 1), (327839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (11, 1), (17, 1), (23, 1), (327839, 1)] : List FactorBlock).map factorBlockValue).prod) = 414550448467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_23
      · exact prime_oneHundredSixtySixFH_327839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 414550448467) ^ 207275224233 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 414550448467) ^ 138183482822 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 414550448467) ^ 59221492638 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 414550448467) ^ 37686404406 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 414550448467) ^ 24385320498 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 414550448467) ^ 18023932542 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 414550448467) ^ 1264494 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_453935900009 : Nat.Prime 453935900009 := by
  apply lucas_primality 453935900009 (3 : ZMod 453935900009)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (64171, 1), (884231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (64171, 1), (884231, 1)] : List FactorBlock).map factorBlockValue).prod) = 453935900009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_64171
      · exact prime_oneHundredSixtySixFH_884231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 453935900009) ^ 226967950004 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 453935900009) ^ 7073848 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 453935900009) ^ 513368 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_625523501861 : Nat.Prime 625523501861 := by
  apply lucas_primality 625523501861 (2 : ZMod 625523501861)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31276175093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31276175093, 1)] : List FactorBlock).map factorBlockValue).prod) = 625523501861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_31276175093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 625523501861) ^ 312761750930 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 625523501861) ^ 125104700372 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 625523501861) ^ 20 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_641143194221 : Nat.Prime 641143194221 := by
  apply lucas_primality 641143194221 (2 : ZMod 641143194221)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (337, 1), (95125103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (337, 1), (95125103, 1)] : List FactorBlock).map factorBlockValue).prod) = 641143194221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_337
      · exact prime_oneHundredSixtySixFH_95125103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 641143194221) ^ 320571597110 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 641143194221) ^ 128228638844 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 641143194221) ^ 1902502060 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 641143194221) ^ 6740 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_696986943733 : Nat.Prime 696986943733 := by
  apply lucas_primality 696986943733 (5 : ZMod 696986943733)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (229, 1), (84544753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (229, 1), (84544753, 1)] : List FactorBlock).map factorBlockValue).prod) = 696986943733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_229
      · exact prime_oneHundredSixtySixFH_84544753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 696986943733) ^ 348493471866 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 696986943733) ^ 232328981244 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 696986943733) ^ 3043611108 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 696986943733) ^ 8244 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_718220178881 : Nat.Prime 718220178881 := by
  apply lucas_primality 718220178881 (3 : ZMod 718220178881)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (101, 1), (661, 1), (33619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (101, 1), (661, 1), (33619, 1)] : List FactorBlock).map factorBlockValue).prod) = 718220178881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_101
      · exact prime_oneHundredSixtySixFH_661
      · exact prime_oneHundredSixtySixFH_33619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 718220178881) ^ 359110089440 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 718220178881) ^ 143644035776 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 718220178881) ^ 7111090880 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 718220178881) ^ 1086566080 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 718220178881) ^ 21363520 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_762794478863 : Nat.Prime 762794478863 := by
  apply lucas_primality 762794478863 (7 : ZMod 762794478863)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (463, 1), (4874273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (463, 1), (4874273, 1)] : List FactorBlock).map factorBlockValue).prod) = 762794478863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_463
      · exact prime_oneHundredSixtySixFH_4874273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 762794478863) ^ 381397239431 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 762794478863) ^ 58676498374 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 762794478863) ^ 1647504274 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 762794478863) ^ 156494 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_935302976263 : Nat.Prime 935302976263 := by
  apply lucas_primality 935302976263 (3 : ZMod 935302976263)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (59, 1), (38291287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (59, 1), (38291287, 1)] : List FactorBlock).map factorBlockValue).prod) = 935302976263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_23
      · exact prime_oneHundredSixtySixFH_59
      · exact prime_oneHundredSixtySixFH_38291287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 935302976263) ^ 467651488131 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 935302976263) ^ 311767658754 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 935302976263) ^ 40665346794 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 935302976263) ^ 15852592818 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 935302976263) ^ 24426 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_946397280701 : Nat.Prime 946397280701 := by
  apply lucas_primality 946397280701 (2 : ZMod 946397280701)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (8273, 1), (1143959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (8273, 1), (1143959, 1)] : List FactorBlock).map factorBlockValue).prod) = 946397280701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_8273
      · exact prime_oneHundredSixtySixFH_1143959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 946397280701) ^ 473198640350 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 946397280701) ^ 189279456140 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 946397280701) ^ 114395900 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 946397280701) ^ 827300 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1373897855507 : Nat.Prime 1373897855507 := by
  apply lucas_primality 1373897855507 (2 : ZMod 1373897855507)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (179, 1), (348882137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (179, 1), (348882137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1373897855507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_179
      · exact prime_oneHundredSixtySixFH_348882137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1373897855507) ^ 686948927753 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1373897855507) ^ 124899805046 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1373897855507) ^ 7675407014 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1373897855507) ^ 3938 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1413946219451 : Nat.Prime 1413946219451 := by
  apply lucas_primality 1413946219451 (2 : ZMod 1413946219451)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19949, 1), (1417561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19949, 1), (1417561, 1)] : List FactorBlock).map factorBlockValue).prod) = 1413946219451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_19949
      · exact prime_oneHundredSixtySixFH_1417561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1413946219451) ^ 706973109725 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1413946219451) ^ 282789243890 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1413946219451) ^ 70878050 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1413946219451) ^ 997450 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1603412956037 : Nat.Prime 1603412956037 := by
  apply lucas_primality 1603412956037 (2 : ZMod 1603412956037)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37993, 1), (10550713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37993, 1), (10550713, 1)] : List FactorBlock).map factorBlockValue).prod) = 1603412956037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_37993
      · exact prime_oneHundredSixtySixFH_10550713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1603412956037) ^ 801706478018 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1603412956037) ^ 42202852 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1603412956037) ^ 151972 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1645038914297 : Nat.Prime 1645038914297 := by
  apply lucas_primality 1645038914297 (3 : ZMod 1645038914297)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (205629864287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (205629864287, 1)] : List FactorBlock).map factorBlockValue).prod) = 1645038914297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_205629864287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1645038914297) ^ 822519457148 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1645038914297) ^ 8 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1892794561403 : Nat.Prime 1892794561403 := by
  apply lucas_primality 1892794561403 (2 : ZMod 1892794561403)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (946397280701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (946397280701, 1)] : List FactorBlock).map factorBlockValue).prod) = 1892794561403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_946397280701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1892794561403) ^ 946397280701 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1892794561403) ^ 2 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_3922808311181 : Nat.Prime 3922808311181 := by
  apply lucas_primality 3922808311181 (2 : ZMod 3922808311181)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (43, 1), (223, 1), (1859521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (43, 1), (223, 1), (1859521, 1)] : List FactorBlock).map factorBlockValue).prod) = 3922808311181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_43
      · exact prime_oneHundredSixtySixFH_223
      · exact prime_oneHundredSixtySixFH_1859521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3922808311181) ^ 1961404155590 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3922808311181) ^ 784561662236 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3922808311181) ^ 356618937380 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3922808311181) ^ 91228100260 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3922808311181) ^ 17591068660 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3922808311181) ^ 2109580 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_4064129142461 : Nat.Prime 4064129142461 := by
  apply lucas_primality 4064129142461 (2 : ZMod 4064129142461)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (547, 1), (8639363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (547, 1), (8639363, 1)] : List FactorBlock).map factorBlockValue).prod) = 4064129142461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_43
      · exact prime_oneHundredSixtySixFH_547
      · exact prime_oneHundredSixtySixFH_8639363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4064129142461) ^ 2032064571230 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4064129142461) ^ 812825828492 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4064129142461) ^ 94514631220 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4064129142461) ^ 7429852180 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4064129142461) ^ 470420 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_4663210013743 : Nat.Prime 4663210013743 := by
  apply lucas_primality 4663210013743 (3 : ZMod 4663210013743)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (332903, 1), (333517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (332903, 1), (333517, 1)] : List FactorBlock).map factorBlockValue).prod) = 4663210013743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_332903
      · exact prime_oneHundredSixtySixFH_333517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4663210013743) ^ 2331605006871 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4663210013743) ^ 1554403337914 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4663210013743) ^ 666172859106 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4663210013743) ^ 14007714 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4663210013743) ^ 13981926 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_4839724377991 : Nat.Prime 4839724377991 := by
  apply lucas_primality 4839724377991 (6 : ZMod 4839724377991)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (2389, 1), (22509299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (2389, 1), (22509299, 1)] : List FactorBlock).map factorBlockValue).prod) = 4839724377991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_2389
      · exact prime_oneHundredSixtySixFH_22509299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4839724377991) ^ 2419862188995 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 4839724377991) ^ 1613241459330 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 4839724377991) ^ 967944875598 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 4839724377991) ^ 2025836910 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 4839724377991) ^ 215010 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_5215986156383 : Nat.Prime 5215986156383 := by
  apply lucas_primality 5215986156383 (5 : ZMod 5215986156383)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (6257, 1), (21937477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (6257, 1), (21937477, 1)] : List FactorBlock).map factorBlockValue).prod) = 5215986156383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_6257
      · exact prime_oneHundredSixtySixFH_21937477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5215986156383) ^ 2607993078191 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5215986156383) ^ 274525587178 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5215986156383) ^ 833624126 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5215986156383) ^ 237766 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_5357681746663 : Nat.Prime 5357681746663 := by
  apply lucas_primality 5357681746663 (3 : ZMod 5357681746663)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (127563851111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (127563851111, 1)] : List FactorBlock).map factorBlockValue).prod) = 5357681746663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_127563851111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5357681746663) ^ 2678840873331 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5357681746663) ^ 1785893915554 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5357681746663) ^ 765383106666 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5357681746663) ^ 42 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_5393737997173 : Nat.Prime 5393737997173 := by
  apply lucas_primality 5393737997173 (2 : ZMod 5393737997173)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (17, 1), (1259042483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (17, 1), (1259042483, 1)] : List FactorBlock).map factorBlockValue).prod) = 5393737997173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_1259042483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5393737997173) ^ 2696868998586 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5393737997173) ^ 1797912665724 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5393737997173) ^ 770533999596 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5393737997173) ^ 317278705716 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5393737997173) ^ 4284 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_5551596661927 : Nat.Prime 5551596661927 := by
  apply lucas_primality 5551596661927 (3 : ZMod 5551596661927)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (122869, 1), (1075787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (122869, 1), (1075787, 1)] : List FactorBlock).map factorBlockValue).prod) = 5551596661927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_122869
      · exact prime_oneHundredSixtySixFH_1075787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5551596661927) ^ 2775798330963 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5551596661927) ^ 1850532220642 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5551596661927) ^ 793085237418 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5551596661927) ^ 45183054 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5551596661927) ^ 5160498 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_6628707031559 : Nat.Prime 6628707031559 := by
  apply lucas_primality 6628707031559 (7 : ZMod 6628707031559)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (509, 1), (14969, 1), (18913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (509, 1), (14969, 1), (18913, 1)] : List FactorBlock).map factorBlockValue).prod) = 6628707031559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_23
      · exact prime_oneHundredSixtySixFH_509
      · exact prime_oneHundredSixtySixFH_14969
      · exact prime_oneHundredSixtySixFH_18913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6628707031559) ^ 3314353515779 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6628707031559) ^ 288204653546 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6628707031559) ^ 13023000062 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6628707031559) ^ 442828982 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6628707031559) ^ 350484166 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_7949397798341 : Nat.Prime 7949397798341 := by
  apply lucas_primality 7949397798341 (2 : ZMod 7949397798341)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (65167, 1), (210319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (65167, 1), (210319, 1)] : List FactorBlock).map factorBlockValue).prod) = 7949397798341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_29
      · exact prime_oneHundredSixtySixFH_65167
      · exact prime_oneHundredSixtySixFH_210319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7949397798341) ^ 3974698899170 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7949397798341) ^ 1589879559668 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7949397798341) ^ 274117165460 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7949397798341) ^ 121985020 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7949397798341) ^ 37796860 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_7973332828259 : Nat.Prime 7973332828259 := by
  apply lucas_primality 7973332828259 (2 : ZMod 7973332828259)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (127, 1), (4484439161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (127, 1), (4484439161, 1)] : List FactorBlock).map factorBlockValue).prod) = 7973332828259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_127
      · exact prime_oneHundredSixtySixFH_4484439161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7973332828259) ^ 3986666414129 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7973332828259) ^ 1139047546894 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7973332828259) ^ 62782148254 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7973332828259) ^ 1778 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_10431972312767 : Nat.Prime 10431972312767 := by
  apply lucas_primality 10431972312767 (5 : ZMod 10431972312767)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5215986156383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5215986156383, 1)] : List FactorBlock).map factorBlockValue).prod) = 10431972312767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5215986156383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 10431972312767) ^ 5215986156383 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 10431972312767) ^ 2 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_10596753118267 : Nat.Prime 10596753118267 := by
  apply lucas_primality 10596753118267 (2 : ZMod 10596753118267)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (252303645673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (252303645673, 1)] : List FactorBlock).map factorBlockValue).prod) = 10596753118267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_252303645673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10596753118267) ^ 5298376559133 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10596753118267) ^ 3532251039422 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10596753118267) ^ 1513821874038 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10596753118267) ^ 42 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_11326193609743 : Nat.Prime 11326193609743 := by
  apply lucas_primality 11326193609743 (3 : ZMod 11326193609743)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (17, 1), (3364882237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (17, 1), (3364882237, 1)] : List FactorBlock).map factorBlockValue).prod) = 11326193609743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_3364882237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11326193609743) ^ 5663096804871 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 11326193609743) ^ 3775397869914 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 11326193609743) ^ 1029653964522 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 11326193609743) ^ 666246682926 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 11326193609743) ^ 3366 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_12877150743701 : Nat.Prime 12877150743701 := by
  apply lucas_primality 12877150743701 (2 : ZMod 12877150743701)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (128771507437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (128771507437, 1)] : List FactorBlock).map factorBlockValue).prod) = 12877150743701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_128771507437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12877150743701) ^ 6438575371850 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12877150743701) ^ 2575430148740 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12877150743701) ^ 100 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_13618077000271 : Nat.Prime 13618077000271 := by
  apply lucas_primality 13618077000271 (3 : ZMod 13618077000271)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (453935900009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (453935900009, 1)] : List FactorBlock).map factorBlockValue).prod) = 13618077000271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_453935900009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13618077000271) ^ 6809038500135 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13618077000271) ^ 4539359000090 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13618077000271) ^ 2723615400054 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13618077000271) ^ 30 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_19567376924701 : Nat.Prime 19567376924701 := by
  apply lucas_primality 19567376924701 (2 : ZMod 19567376924701)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 1), (5929508159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 1), (5929508159, 1)] : List FactorBlock).map factorBlockValue).prod) = 19567376924701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_5929508159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19567376924701) ^ 9783688462350 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 19567376924701) ^ 6522458974900 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 19567376924701) ^ 3913475384940 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 19567376924701) ^ 1778852447700 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 19567376924701) ^ 3300 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_21863714157457 : Nat.Prime 21863714157457 := by
  apply lucas_primality 21863714157457 (5 : ZMod 21863714157457)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (311, 1), (1464611077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (311, 1), (1464611077, 1)] : List FactorBlock).map factorBlockValue).prod) = 21863714157457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_311
      · exact prime_oneHundredSixtySixFH_1464611077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21863714157457) ^ 10931857078728 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 21863714157457) ^ 7287904719152 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 21863714157457) ^ 70301331696 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 21863714157457) ^ 14928 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_27285408661969 : Nat.Prime 27285408661969 := by
  apply lucas_primality 27285408661969 (14 : ZMod 27285408661969)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (63160668199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (63160668199, 1)] : List FactorBlock).map factorBlockValue).prod) = 27285408661969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_63160668199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 27285408661969) ^ 13642704330984 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (14 : ZMod 27285408661969) ^ 9095136220656 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (14 : ZMod 27285408661969) ^ 432 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_30036009397841 : Nat.Prime 30036009397841 := by
  apply lucas_primality 30036009397841 (3 : ZMod 30036009397841)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (23, 1), (211, 1), (853, 1), (90697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (23, 1), (211, 1), (853, 1), (90697, 1)] : List FactorBlock).map factorBlockValue).prod) = 30036009397841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_23
      · exact prime_oneHundredSixtySixFH_211
      · exact prime_oneHundredSixtySixFH_853
      · exact prime_oneHundredSixtySixFH_90697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30036009397841) ^ 15018004698920 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 30036009397841) ^ 6007201879568 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 30036009397841) ^ 1305913452080 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 30036009397841) ^ 142350755440 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 30036009397841) ^ 35212203280 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 30036009397841) ^ 331168720 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_32639972703869 : Nat.Prime 32639972703869 := by
  apply lucas_primality 32639972703869 (2 : ZMod 32639972703869)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (114343, 1), (71364169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (114343, 1), (71364169, 1)] : List FactorBlock).map factorBlockValue).prod) = 32639972703869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_114343
      · exact prime_oneHundredSixtySixFH_71364169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32639972703869) ^ 16319986351934 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 32639972703869) ^ 285456676 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 32639972703869) ^ 457372 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_43958533532647 : Nat.Prime 43958533532647 := by
  apply lucas_primality 43958533532647 (5 : ZMod 43958533532647)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (311, 1), (433, 1), (2863453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (311, 1), (433, 1), (2863453, 1)] : List FactorBlock).map factorBlockValue).prod) = 43958533532647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_311
      · exact prime_oneHundredSixtySixFH_433
      · exact prime_oneHundredSixtySixFH_2863453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 43958533532647) ^ 21979266766323 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 43958533532647) ^ 14652844510882 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 43958533532647) ^ 2313607028034 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 43958533532647) ^ 141345766986 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 43958533532647) ^ 101520862662 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 43958533532647) ^ 15351582 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_65279945407739 : Nat.Prime 65279945407739 := by
  apply lucas_primality 65279945407739 (2 : ZMod 65279945407739)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32639972703869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32639972703869, 1)] : List FactorBlock).map factorBlockValue).prod) = 65279945407739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_32639972703869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 65279945407739) ^ 32639972703869 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 65279945407739) ^ 2 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_70572033622357 : Nat.Prime 70572033622357 := by
  apply lucas_primality 70572033622357 (2 : ZMod 70572033622357)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (89, 1), (9439811881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (89, 1), (9439811881, 1)] : List FactorBlock).map factorBlockValue).prod) = 70572033622357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_89
      · exact prime_oneHundredSixtySixFH_9439811881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70572033622357) ^ 35286016811178 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 70572033622357) ^ 23524011207452 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 70572033622357) ^ 10081719088908 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 70572033622357) ^ 792944198004 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 70572033622357) ^ 7476 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_103711135101401 : Nat.Prime 103711135101401 := by
  apply lucas_primality 103711135101401 (3 : ZMod 103711135101401)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (1733, 1), (2341, 1), (127819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (1733, 1), (2341, 1), (127819, 1)] : List FactorBlock).map factorBlockValue).prod) = 103711135101401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_1733
      · exact prime_oneHundredSixtySixFH_2341
      · exact prime_oneHundredSixtySixFH_127819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 103711135101401) ^ 51855567550700 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 103711135101401) ^ 20742227020280 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 103711135101401) ^ 59844855800 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 103711135101401) ^ 44302065400 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 103711135101401) ^ 811390600 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_112393088372779 : Nat.Prime 112393088372779 := by
  apply lucas_primality 112393088372779 (2 : ZMod 112393088372779)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (541, 1), (1567, 1), (22096429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (541, 1), (1567, 1), (22096429, 1)] : List FactorBlock).map factorBlockValue).prod) = 112393088372779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_541
      · exact prime_oneHundredSixtySixFH_1567
      · exact prime_oneHundredSixtySixFH_22096429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 112393088372779) ^ 56196544186389 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 112393088372779) ^ 37464362790926 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 112393088372779) ^ 207750625458 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 112393088372779) ^ 71725008534 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 112393088372779) ^ 5086482 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_247741289789569 : Nat.Prime 247741289789569 := by
  apply lucas_primality 247741289789569 (23 : ZMod 247741289789569)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (29, 1), (71411, 1), (311533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (29, 1), (71411, 1), (311533, 1)] : List FactorBlock).map factorBlockValue).prod) = 247741289789569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_29
      · exact prime_oneHundredSixtySixFH_71411
      · exact prime_oneHundredSixtySixFH_311533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 247741289789569) ^ 123870644894784 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (23 : ZMod 247741289789569) ^ 82580429929856 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (23 : ZMod 247741289789569) ^ 8542803096192 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (23 : ZMod 247741289789569) ^ 3469231488 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (23 : ZMod 247741289789569) ^ 795232896 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_360815091211451 : Nat.Prime 360815091211451 := by
  apply lucas_primality 360815091211451 (2 : ZMod 360815091211451)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (53, 1), (773, 1), (176140541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (53, 1), (773, 1), (176140541, 1)] : List FactorBlock).map factorBlockValue).prod) = 360815091211451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_53
      · exact prime_oneHundredSixtySixFH_773
      · exact prime_oneHundredSixtySixFH_176140541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 360815091211451) ^ 180407545605725 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 360815091211451) ^ 72163018242290 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 360815091211451) ^ 6807831909650 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 360815091211451) ^ 466772433650 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 360815091211451) ^ 2048450 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_402411407710181 : Nat.Prime 402411407710181 := by
  apply lucas_primality 402411407710181 (2 : ZMod 402411407710181)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (19, 1), (271, 1), (355242331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (19, 1), (271, 1), (355242331, 1)] : List FactorBlock).map factorBlockValue).prod) = 402411407710181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_271
      · exact prime_oneHundredSixtySixFH_355242331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 402411407710181) ^ 201205703855090 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 402411407710181) ^ 80482281542036 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 402411407710181) ^ 36582855246380 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 402411407710181) ^ 21179547774220 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 402411407710181) ^ 1484912943580 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 402411407710181) ^ 1132780 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_420721041685171 : Nat.Prime 420721041685171 := by
  apply lucas_primality 420721041685171 (10 : ZMod 420721041685171)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (108971, 1), (1274209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (108971, 1), (1274209, 1)] : List FactorBlock).map factorBlockValue).prod) = 420721041685171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_101
      · exact prime_oneHundredSixtySixFH_108971
      · exact prime_oneHundredSixtySixFH_1274209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 420721041685171) ^ 210360520842585 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 420721041685171) ^ 140240347228390 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 420721041685171) ^ 84144208337034 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 420721041685171) ^ 4165554868170 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 420721041685171) ^ 3860853270 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 420721041685171) ^ 330182130 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_469700051604569 : Nat.Prime 469700051604569 := by
  apply lucas_primality 469700051604569 (3 : ZMod 469700051604569)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1621, 1), (36219929951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1621, 1), (36219929951, 1)] : List FactorBlock).map factorBlockValue).prod) = 469700051604569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_1621
      · exact prime_oneHundredSixtySixFH_36219929951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 469700051604569) ^ 234850025802284 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 469700051604569) ^ 289759439608 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 469700051604569) ^ 12968 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_923131888658219 : Nat.Prime 923131888658219 := by
  apply lucas_primality 923131888658219 (2 : ZMod 923131888658219)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29383, 1), (15708605123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29383, 1), (15708605123, 1)] : List FactorBlock).map factorBlockValue).prod) = 923131888658219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_29383
      · exact prime_oneHundredSixtySixFH_15708605123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 923131888658219) ^ 461565944329109 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 923131888658219) ^ 31417210246 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 923131888658219) ^ 58766 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_950146276717679 : Nat.Prime 950146276717679 := by
  apply lucas_primality 950146276717679 (13 : ZMod 950146276717679)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (787, 1), (98317, 1), (142787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (787, 1), (98317, 1), (142787, 1)] : List FactorBlock).map factorBlockValue).prod) = 950146276717679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_43
      · exact prime_oneHundredSixtySixFH_787
      · exact prime_oneHundredSixtySixFH_98317
      · exact prime_oneHundredSixtySixFH_142787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 950146276717679) ^ 475073138358839 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 950146276717679) ^ 22096425039946 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 950146276717679) ^ 1207301495194 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 950146276717679) ^ 9664109734 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 950146276717679) ^ 6654291194 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1067152290403373 : Nat.Prime 1067152290403373 := by
  apply lucas_primality 1067152290403373 (2 : ZMod 1067152290403373)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (3739, 1), (859672139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (3739, 1), (859672139, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067152290403373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_83
      · exact prime_oneHundredSixtySixFH_3739
      · exact prime_oneHundredSixtySixFH_859672139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1067152290403373) ^ 533576145201686 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067152290403373) ^ 12857256510884 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067152290403373) ^ 285411150148 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067152290403373) ^ 1241348 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1172469949234931 : Nat.Prime 1172469949234931 := by
  apply lucas_primality 1172469949234931 (2 : ZMod 1172469949234931)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (13879, 1), (118983077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (13879, 1), (118983077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1172469949234931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_71
      · exact prime_oneHundredSixtySixFH_13879
      · exact prime_oneHundredSixtySixFH_118983077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1172469949234931) ^ 586234974617465 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172469949234931) ^ 234493989846986 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172469949234931) ^ 16513661256830 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172469949234931) ^ 84477984670 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172469949234931) ^ 9854090 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1371566527145729 : Nat.Prime 1371566527145729 := by
  apply lucas_primality 1371566527145729 (3 : ZMod 1371566527145729)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5357681746663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5357681746663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1371566527145729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5357681746663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1371566527145729) ^ 685783263572864 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1371566527145729) ^ 256 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1473412067746327 : Nat.Prime 1473412067746327 := by
  apply lucas_primality 1473412067746327 (3 : ZMod 1473412067746327)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (27285408661969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (27285408661969, 1)] : List FactorBlock).map factorBlockValue).prod) = 1473412067746327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_27285408661969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1473412067746327) ^ 736706033873163 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473412067746327) ^ 491137355915442 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473412067746327) ^ 54 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1710269308072553 : Nat.Prime 1710269308072553 := by
  apply lucas_primality 1710269308072553 (3 : ZMod 1710269308072553)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (27997, 1), (144074509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (27997, 1), (144074509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1710269308072553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_53
      · exact prime_oneHundredSixtySixFH_27997
      · exact prime_oneHundredSixtySixFH_144074509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1710269308072553) ^ 855134654036276 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1710269308072553) ^ 32269232227784 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1710269308072553) ^ 61087591816 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1710269308072553) ^ 11870728 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_2040662234661287 : Nat.Prime 2040662234661287 := by
  apply lucas_primality 2040662234661287 (5 : ZMod 2040662234661287)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8586181, 1), (118834103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8586181, 1), (118834103, 1)] : List FactorBlock).map factorBlockValue).prod) = 2040662234661287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_8586181
      · exact prime_oneHundredSixtySixFH_118834103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2040662234661287) ^ 1020331117330643 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2040662234661287) ^ 237668206 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 2040662234661287) ^ 17172362 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_2256207514756751 : Nat.Prime 2256207514756751 := by
  apply lucas_primality 2256207514756751 (19 : ZMod 2256207514756751)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (233, 1), (144139, 1), (268721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (233, 1), (144139, 1), (268721, 1)] : List FactorBlock).map factorBlockValue).prod) = 2256207514756751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_233
      · exact prime_oneHundredSixtySixFH_144139
      · exact prime_oneHundredSixtySixFH_268721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 2256207514756751) ^ 1128103757378375 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (19 : ZMod 2256207514756751) ^ 451241502951350 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (19 : ZMod 2256207514756751) ^ 9683294054750 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (19 : ZMod 2256207514756751) ^ 15652998250 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (19 : ZMod 2256207514756751) ^ 8396096750 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_2743133054291459 : Nat.Prime 2743133054291459 := by
  apply lucas_primality 2743133054291459 (2 : ZMod 2743133054291459)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1371566527145729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1371566527145729, 1)] : List FactorBlock).map factorBlockValue).prod) = 2743133054291459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_1371566527145729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2743133054291459) ^ 1371566527145729 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2743133054291459) ^ 2 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_2787251025765403 : Nat.Prime 2787251025765403 := by
  apply lucas_primality 2787251025765403 (3 : ZMod 2787251025765403)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (29, 1), (762794478863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (29, 1), (762794478863, 1)] : List FactorBlock).map factorBlockValue).prod) = 2787251025765403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_29
      · exact prime_oneHundredSixtySixFH_762794478863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2787251025765403) ^ 1393625512882701 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2787251025765403) ^ 929083675255134 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2787251025765403) ^ 398178717966486 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2787251025765403) ^ 96112104336738 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2787251025765403) ^ 3654 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_2858727465101623 : Nat.Prime 2858727465101623 := by
  apply lucas_primality 2858727465101623 (3 : ZMod 2858727465101623)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (12877150743701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (12877150743701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2858727465101623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_37
      · exact prime_oneHundredSixtySixFH_12877150743701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2858727465101623) ^ 1429363732550811 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2858727465101623) ^ 952909155033874 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2858727465101623) ^ 77262904462206 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2858727465101623) ^ 222 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_3119317856731969 : Nat.Prime 3119317856731969 := by
  apply lucas_primality 3119317856731969 (11 : ZMod 3119317856731969)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (101, 1), (5231, 1), (30750509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (101, 1), (5231, 1), (30750509, 1)] : List FactorBlock).map factorBlockValue).prod) = 3119317856731969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_101
      · exact prime_oneHundredSixtySixFH_5231
      · exact prime_oneHundredSixtySixFH_30750509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3119317856731969) ^ 1559658928365984 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3119317856731969) ^ 1039772618910656 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3119317856731969) ^ 30884335215168 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3119317856731969) ^ 596313870528 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 3119317856731969) ^ 101439552 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_3934410139910119 : Nat.Prime 3934410139910119 := by
  apply lucas_primality 3934410139910119 (3 : ZMod 3934410139910119)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (83, 1), (718220178881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (83, 1), (718220178881, 1)] : List FactorBlock).map factorBlockValue).prod) = 3934410139910119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_83
      · exact prime_oneHundredSixtySixFH_718220178881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3934410139910119) ^ 1967205069955059 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3934410139910119) ^ 1311470046636706 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3934410139910119) ^ 357673649082738 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3934410139910119) ^ 47402531806146 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3934410139910119) ^ 5478 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_5721027051963583 : Nat.Prime 5721027051963583 := by
  apply lucas_primality 5721027051963583 (6 : ZMod 5721027051963583)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (139, 1), (167, 1), (1039, 1), (4392719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (139, 1), (167, 1), (1039, 1), (4392719, 1)] : List FactorBlock).map factorBlockValue).prod) = 5721027051963583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_139
      · exact prime_oneHundredSixtySixFH_167
      · exact prime_oneHundredSixtySixFH_1039
      · exact prime_oneHundredSixtySixFH_4392719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5721027051963583) ^ 2860513525981791 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 5721027051963583) ^ 1907009017321194 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 5721027051963583) ^ 41158467999738 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 5721027051963583) ^ 34257647017746 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 5721027051963583) ^ 5506282051938 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 5721027051963583) ^ 1302388578 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_6208554457898603 : Nat.Prime 6208554457898603 := by
  apply lucas_primality 6208554457898603 (2 : ZMod 6208554457898603)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (131, 1), (677, 1), (1039, 1), (821677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (131, 1), (677, 1), (1039, 1), (821677, 1)] : List FactorBlock).map factorBlockValue).prod) = 6208554457898603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_41
      · exact prime_oneHundredSixtySixFH_131
      · exact prime_oneHundredSixtySixFH_677
      · exact prime_oneHundredSixtySixFH_1039
      · exact prime_oneHundredSixtySixFH_821677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6208554457898603) ^ 3104277228949301 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6208554457898603) ^ 151428157509722 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6208554457898603) ^ 47393545480142 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6208554457898603) ^ 9170686053026 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6208554457898603) ^ 5975509584118 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 6208554457898603) ^ 7555955026 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_6980625554123167 : Nat.Prime 6980625554123167 := by
  apply lucas_primality 6980625554123167 (5 : ZMod 6980625554123167)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (7546069, 1), (14016179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (7546069, 1), (14016179, 1)] : List FactorBlock).map factorBlockValue).prod) = 6980625554123167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_7546069
      · exact prime_oneHundredSixtySixFH_14016179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6980625554123167) ^ 3490312777061583 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6980625554123167) ^ 2326875184707722 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6980625554123167) ^ 634602323102106 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6980625554123167) ^ 925067814 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6980625554123167) ^ 498040554 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_8613608449555973 : Nat.Prime 8613608449555973 := by
  apply lucas_primality 8613608449555973 (2 : ZMod 8613608449555973)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 2), (77213313937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 2), (77213313937, 1)] : List FactorBlock).map factorBlockValue).prod) = 8613608449555973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_167
      · exact prime_oneHundredSixtySixFH_77213313937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8613608449555973) ^ 4306804224777986 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8613608449555973) ^ 51578493709916 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8613608449555973) ^ 111556 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_9856061574361127 : Nat.Prime 9856061574361127 := by
  apply lucas_primality 9856061574361127 (5 : ZMod 9856061574361127)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (2141261, 1), (43423811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (2141261, 1), (43423811, 1)] : List FactorBlock).map factorBlockValue).prod) = 9856061574361127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_53
      · exact prime_oneHundredSixtySixFH_2141261
      · exact prime_oneHundredSixtySixFH_43423811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9856061574361127) ^ 4928030787180563 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9856061574361127) ^ 185963425931342 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9856061574361127) ^ 4602923966 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 9856061574361127) ^ 226973666 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_11337174003609767 : Nat.Prime 11337174003609767 := by
  apply lucas_primality 11337174003609767 (5 : ZMod 11337174003609767)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (32089, 1), (95891, 1), (141709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (32089, 1), (95891, 1), (141709, 1)] : List FactorBlock).map factorBlockValue).prod) = 11337174003609767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_32089
      · exact prime_oneHundredSixtySixFH_95891
      · exact prime_oneHundredSixtySixFH_141709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11337174003609767) ^ 5668587001804883 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11337174003609767) ^ 872090307969982 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11337174003609767) ^ 353304060694 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11337174003609767) ^ 118229802626 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 11337174003609767) ^ 80003203774 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_12959518308934817 : Nat.Prime 12959518308934817 := by
  apply lucas_primality 12959518308934817 (3 : ZMod 12959518308934817)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (313, 1), (829, 1), (1560773969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (313, 1), (829, 1), (1560773969, 1)] : List FactorBlock).map factorBlockValue).prod) = 12959518308934817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_313
      · exact prime_oneHundredSixtySixFH_829
      · exact prime_oneHundredSixtySixFH_1560773969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12959518308934817) ^ 6479759154467408 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 12959518308934817) ^ 41404211849632 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 12959518308934817) ^ 15632712073504 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 12959518308934817) ^ 8303264 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_13164086306799229 : Nat.Prime 13164086306799229 := by
  apply lucas_primality 13164086306799229 (6 : ZMod 13164086306799229)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (50909, 1), (21548394041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (50909, 1), (21548394041, 1)] : List FactorBlock).map factorBlockValue).prod) = 13164086306799229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_50909
      · exact prime_oneHundredSixtySixFH_21548394041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 13164086306799229) ^ 6582043153399614 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 13164086306799229) ^ 4388028768933076 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 13164086306799229) ^ 258580728492 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 13164086306799229) ^ 610908 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_15964304242953947 : Nat.Prime 15964304242953947 := by
  apply lucas_primality 15964304242953947 (2 : ZMod 15964304242953947)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (43, 1), (9013, 1), (31963, 1), (58579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (43, 1), (9013, 1), (31963, 1), (58579, 1)] : List FactorBlock).map factorBlockValue).prod) = 15964304242953947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_43
      · exact prime_oneHundredSixtySixFH_9013
      · exact prime_oneHundredSixtySixFH_31963
      · exact prime_oneHundredSixtySixFH_58579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15964304242953947) ^ 7982152121476973 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15964304242953947) ^ 1451300385723086 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15964304242953947) ^ 371262889371022 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15964304242953947) ^ 1771253105842 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15964304242953947) ^ 499462010542 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15964304242953947) ^ 272526062974 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_20916485916962333 : Nat.Prime 20916485916962333 := by
  apply lucas_primality 20916485916962333 (2 : ZMod 20916485916962333)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (20107, 1), (15297925157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (20107, 1), (15297925157, 1)] : List FactorBlock).map factorBlockValue).prod) = 20916485916962333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_20107
      · exact prime_oneHundredSixtySixFH_15297925157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20916485916962333) ^ 10458242958481166 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20916485916962333) ^ 1230381524527196 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20916485916962333) ^ 1040258910676 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 20916485916962333) ^ 1367276 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_21757759853982811 : Nat.Prime 21757759853982811 := by
  apply lucas_primality 21757759853982811 (10 : ZMod 21757759853982811)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (61, 1), (21587, 1), (78681523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (61, 1), (21587, 1), (78681523, 1)] : List FactorBlock).map factorBlockValue).prod) = 21757759853982811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_61
      · exact prime_oneHundredSixtySixFH_21587
      · exact prime_oneHundredSixtySixFH_78681523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 21757759853982811) ^ 10878879926991405 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 21757759853982811) ^ 7252586617994270 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 21757759853982811) ^ 4351551970796562 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 21757759853982811) ^ 3108251407711830 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 21757759853982811) ^ 356684587770210 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 21757759853982811) ^ 1007910309630 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 21757759853982811) ^ 276529470 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_35710011321887921 : Nat.Prime 35710011321887921 := by
  apply lucas_primality 35710011321887921 (3 : ZMod 35710011321887921)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (263437, 1), (1694428427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (263437, 1), (1694428427, 1)] : List FactorBlock).map factorBlockValue).prod) = 35710011321887921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_263437
      · exact prime_oneHundredSixtySixFH_1694428427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35710011321887921) ^ 17855005660943960 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35710011321887921) ^ 7142002264377584 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35710011321887921) ^ 135554274160 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35710011321887921) ^ 21074960 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_46120570267448269 : Nat.Prime 46120570267448269 := by
  apply lucas_primality 46120570267448269 (2 : ZMod 46120570267448269)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (47, 1), (1603412956037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (47, 1), (1603412956037, 1)] : List FactorBlock).map factorBlockValue).prod) = 46120570267448269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_47
      · exact prime_oneHundredSixtySixFH_1603412956037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46120570267448269) ^ 23060285133724134 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 46120570267448269) ^ 15373523422482756 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 46120570267448269) ^ 2712974721614604 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 46120570267448269) ^ 981288729094644 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 46120570267448269) ^ 28764 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_59650960550358097 : Nat.Prime 59650960550358097 := by
  apply lucas_primality 59650960550358097 (10 : ZMod 59650960550358097)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (2557, 1), (18000381593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (2557, 1), (18000381593, 1)] : List FactorBlock).map factorBlockValue).prod) = 59650960550358097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_2557
      · exact prime_oneHundredSixtySixFH_18000381593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 59650960550358097) ^ 29825480275179048 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 59650960550358097) ^ 19883653516786032 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 59650960550358097) ^ 23328494544528 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (10 : ZMod 59650960550358097) ^ 3313872 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_77623904950810271 : Nat.Prime 77623904950810271 := by
  apply lucas_primality 77623904950810271 (7 : ZMod 77623904950810271)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (83, 1), (1097, 1), (6557939629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (83, 1), (1097, 1), (6557939629, 1)] : List FactorBlock).map factorBlockValue).prod) = 77623904950810271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_83
      · exact prime_oneHundredSixtySixFH_1097
      · exact prime_oneHundredSixtySixFH_6557939629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 77623904950810271) ^ 38811952475405135 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 77623904950810271) ^ 15524780990162054 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 77623904950810271) ^ 5971069611600790 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 77623904950810271) ^ 935227770491690 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 77623904950810271) ^ 70760168596910 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 77623904950810271) ^ 11836630 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_96687826363073521 : Nat.Prime 96687826363073521 := by
  apply lucas_primality 96687826363073521 (17 : ZMod 96687826363073521)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (5, 1), (83, 1), (179770612753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (5, 1), (83, 1), (179770612753, 1)] : List FactorBlock).map factorBlockValue).prod) = 96687826363073521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_83
      · exact prime_oneHundredSixtySixFH_179770612753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 96687826363073521) ^ 48343913181536760 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 96687826363073521) ^ 32229275454357840 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 96687826363073521) ^ 19337565272614704 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 96687826363073521) ^ 1164913570639440 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 96687826363073521) ^ 537840 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_110801313211341497 : Nat.Prime 110801313211341497 := by
  apply lucas_primality 110801313211341497 (3 : ZMod 110801313211341497)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (416387, 1), (33262719901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (416387, 1), (33262719901, 1)] : List FactorBlock).map factorBlockValue).prod) = 110801313211341497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_416387
      · exact prime_oneHundredSixtySixFH_33262719901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 110801313211341497) ^ 55400656605670748 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 110801313211341497) ^ 266101759208 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 110801313211341497) ^ 3331096 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_115040140797397073 : Nat.Prime 115040140797397073 := by
  apply lucas_primality 115040140797397073 (3 : ZMod 115040140797397073)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (487, 1), (1069, 1), (1459, 1), (9466021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (487, 1), (1069, 1), (1459, 1), (9466021, 1)] : List FactorBlock).map factorBlockValue).prod) = 115040140797397073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_487
      · exact prime_oneHundredSixtySixFH_1069
      · exact prime_oneHundredSixtySixFH_1459
      · exact prime_oneHundredSixtySixFH_9466021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 115040140797397073) ^ 57520070398698536 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 115040140797397073) ^ 236222055025456 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 115040140797397073) ^ 107614724787088 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 115040140797397073) ^ 78848622890608 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 115040140797397073) ^ 12152956432 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_136522462290122423 : Nat.Prime 136522462290122423 := by
  apply lucas_primality 136522462290122423 (5 : ZMod 136522462290122423)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (18749, 1), (117444940969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (18749, 1), (117444940969, 1)] : List FactorBlock).map factorBlockValue).prod) = 136522462290122423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_31
      · exact prime_oneHundredSixtySixFH_18749
      · exact prime_oneHundredSixtySixFH_117444940969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 136522462290122423) ^ 68261231145061211 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 136522462290122423) ^ 4403950396455562 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 136522462290122423) ^ 7281586340078 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 136522462290122423) ^ 1162438 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_147921531993551131 : Nat.Prime 147921531993551131 := by
  apply lucas_primality 147921531993551131 (2 : ZMod 147921531993551131)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (6476963, 1), (40066843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (6476963, 1), (40066843, 1)] : List FactorBlock).map factorBlockValue).prod) = 147921531993551131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_6476963
      · exact prime_oneHundredSixtySixFH_40066843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 147921531993551131) ^ 73960765996775565 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 147921531993551131) ^ 49307177331183710 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 147921531993551131) ^ 29584306398710226 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 147921531993551131) ^ 7785343789134270 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 147921531993551131) ^ 22838100510 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 147921531993551131) ^ 3691868910 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_203058676328107591 : Nat.Prime 203058676328107591 := by
  apply lucas_primality 203058676328107591 (3 : ZMod 203058676328107591)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (2256207514756751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (2256207514756751, 1)] : List FactorBlock).map factorBlockValue).prod) = 203058676328107591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_2256207514756751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 203058676328107591) ^ 101529338164053795 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 203058676328107591) ^ 67686225442702530 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 203058676328107591) ^ 40611735265621518 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 203058676328107591) ^ 90 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_237341268840187679 : Nat.Prime 237341268840187679 := by
  apply lucas_primality 237341268840187679 (13 : ZMod 237341268840187679)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (6980625554123167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (6980625554123167, 1)] : List FactorBlock).map factorBlockValue).prod) = 237341268840187679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_6980625554123167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 237341268840187679) ^ 118670634420093839 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 237341268840187679) ^ 13961251108246334 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (13 : ZMod 237341268840187679) ^ 34 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_274257234013327139 : Nat.Prime 274257234013327139 := by
  apply lucas_primality 274257234013327139 (2 : ZMod 274257234013327139)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (71, 1), (15671, 1), (17606579687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (71, 1), (15671, 1), (17606579687, 1)] : List FactorBlock).map factorBlockValue).prod) = 274257234013327139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_71
      · exact prime_oneHundredSixtySixFH_15671
      · exact prime_oneHundredSixtySixFH_17606579687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 274257234013327139) ^ 137128617006663569 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 274257234013327139) ^ 39179604859046734 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 274257234013327139) ^ 3862777943849678 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 274257234013327139) ^ 17500940208878 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 274257234013327139) ^ 15576974 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_313742773378591663 : Nat.Prime 313742773378591663 := by
  apply lucas_primality 313742773378591663 (3 : ZMod 313742773378591663)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (1067152290403373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (1067152290403373, 1)] : List FactorBlock).map factorBlockValue).prod) = 313742773378591663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_1067152290403373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 313742773378591663) ^ 156871386689295831 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 313742773378591663) ^ 104580924459530554 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 313742773378591663) ^ 44820396196941666 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 313742773378591663) ^ 294 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_317982429885337043 : Nat.Prime 317982429885337043 := by
  apply lucas_primality 317982429885337043 (2 : ZMod 317982429885337043)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4211, 1), (5393737997173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4211, 1), (5393737997173, 1)] : List FactorBlock).map factorBlockValue).prod) = 317982429885337043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_4211
      · exact prime_oneHundredSixtySixFH_5393737997173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 317982429885337043) ^ 158991214942668521 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 317982429885337043) ^ 45426061412191006 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 317982429885337043) ^ 75512331960422 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 317982429885337043) ^ 58954 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_737069974621369177 : Nat.Prime 737069974621369177 := by
  apply lucas_primality 737069974621369177 (5 : ZMod 737069974621369177)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (1973, 1), (38567, 1), (9843979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (1973, 1), (38567, 1), (9843979, 1)] : List FactorBlock).map factorBlockValue).prod) = 737069974621369177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_41
      · exact prime_oneHundredSixtySixFH_1973
      · exact prime_oneHundredSixtySixFH_38567
      · exact prime_oneHundredSixtySixFH_9843979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 737069974621369177) ^ 368534987310684588 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 737069974621369177) ^ 245689991540456392 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 737069974621369177) ^ 17977316454179736 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 737069974621369177) ^ 373578294283512 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 737069974621369177) ^ 19111415837928 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 737069974621369177) ^ 74875207944 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1426252952145226853 : Nat.Prime 1426252952145226853 := by
  apply lucas_primality 1426252952145226853 (2 : ZMod 1426252952145226853)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (10357, 1), (28307, 1), (1216210487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (10357, 1), (28307, 1), (1216210487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1426252952145226853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_10357
      · exact prime_oneHundredSixtySixFH_28307
      · exact prime_oneHundredSixtySixFH_1216210487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1426252952145226853) ^ 713126476072613426 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1426252952145226853) ^ 137709081022036 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1426252952145226853) ^ 50385168055436 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1426252952145226853) ^ 1172702396 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1586035883628851219 : Nat.Prime 1586035883628851219 := by
  apply lucas_primality 1586035883628851219 (6 : ZMod 1586035883628851219)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (661, 1), (70572033622357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (661, 1), (70572033622357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1586035883628851219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_661
      · exact prime_oneHundredSixtySixFH_70572033622357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1586035883628851219) ^ 793017941814425609 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1586035883628851219) ^ 93296228448755954 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1586035883628851219) ^ 2399449143160138 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 1586035883628851219) ^ 22474 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_101
      · exact prime_oneHundredSixtySixFH_191
      · exact prime_oneHundredSixtySixFH_48017
      · exact prime_oneHundredSixtySixFH_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_2977159790395854961 : Nat.Prime 2977159790395854961 := by
  apply lucas_primality 2977159790395854961 (11 : ZMod 2977159790395854961)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (14887, 1), (165811, 1), (386569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (14887, 1), (165811, 1), (386569, 1)] : List FactorBlock).map factorBlockValue).prod) = 2977159790395854961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_14887
      · exact prime_oneHundredSixtySixFH_165811
      · exact prime_oneHundredSixtySixFH_386569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2977159790395854961) ^ 1488579895197927480 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2977159790395854961) ^ 992386596798618320 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2977159790395854961) ^ 595431958079170992 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2977159790395854961) ^ 229012291568911920 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2977159790395854961) ^ 199983864472080 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2977159790395854961) ^ 17955140433360 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2977159790395854961) ^ 7701496473840 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_3188041503997964983 : Nat.Prime 3188041503997964983 := by
  apply lucas_primality 3188041503997964983 (5 : ZMod 3188041503997964983)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (12959518308934817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (12959518308934817, 1)] : List FactorBlock).map factorBlockValue).prod) = 3188041503997964983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_41
      · exact prime_oneHundredSixtySixFH_12959518308934817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3188041503997964983) ^ 1594020751998982491 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3188041503997964983) ^ 1062680501332654994 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3188041503997964983) ^ 77757109853608902 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 3188041503997964983) ^ 246 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_3610591921017462991 : Nat.Prime 3610591921017462991 := by
  apply lucas_primality 3610591921017462991 (7 : ZMod 3610591921017462991)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (163, 1), (5551596661927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (163, 1), (5551596661927, 1)] : List FactorBlock).map factorBlockValue).prod) = 3610591921017462991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_163
      · exact prime_oneHundredSixtySixFH_5551596661927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3610591921017462991) ^ 1805295960508731495 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3610591921017462991) ^ 1203530640339154330 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3610591921017462991) ^ 722118384203492598 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3610591921017462991) ^ 515798845859637570 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3610591921017462991) ^ 190031153737761210 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3610591921017462991) ^ 22150870681088730 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 3610591921017462991) ^ 650370 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_6746245607888531183 : Nat.Prime 6746245607888531183 := by
  apply lucas_primality 6746245607888531183 (5 : ZMod 6746245607888531183)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (241, 1), (1637, 1), (108227926837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (241, 1), (1637, 1), (108227926837, 1)] : List FactorBlock).map factorBlockValue).prod) = 6746245607888531183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_79
      · exact prime_oneHundredSixtySixFH_241
      · exact prime_oneHundredSixtySixFH_1637
      · exact prime_oneHundredSixtySixFH_108227926837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6746245607888531183) ^ 3373122803944265591 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6746245607888531183) ^ 85395514023905458 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6746245607888531183) ^ 27992720364682702 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6746245607888531183) ^ 4121102998099286 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6746245607888531183) ^ 62333686 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_7448965708481337269 : Nat.Prime 7448965708481337269 := by
  apply lucas_primality 7448965708481337269 (2 : ZMod 7448965708481337269)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (164419, 1), (11326193609743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (164419, 1), (11326193609743, 1)] : List FactorBlock).map factorBlockValue).prod) = 7448965708481337269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_164419
      · exact prime_oneHundredSixtySixFH_11326193609743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7448965708481337269) ^ 3724482854240668634 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7448965708481337269) ^ 45304774438972 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7448965708481337269) ^ 657676 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_7923330455266329023 : Nat.Prime 7923330455266329023 := by
  apply lucas_primality 7923330455266329023 (5 : ZMod 7923330455266329023)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (199, 1), (64372951, 1), (309258239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (199, 1), (64372951, 1), (309258239, 1)] : List FactorBlock).map factorBlockValue).prod) = 7923330455266329023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_199
      · exact prime_oneHundredSixtySixFH_64372951
      · exact prime_oneHundredSixtySixFH_309258239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7923330455266329023) ^ 3961665227633164511 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7923330455266329023) ^ 39815730930986578 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7923330455266329023) ^ 123084779122 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7923330455266329023) ^ 25620434498 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_15564532260361971239 : Nat.Prime 15564532260361971239 := by
  apply lucas_primality 15564532260361971239 (11 : ZMod 15564532260361971239)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (53, 1), (467, 1), (509, 1), (3303345043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (53, 1), (467, 1), (509, 1), (3303345043, 1)] : List FactorBlock).map factorBlockValue).prod) = 15564532260361971239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_53
      · exact prime_oneHundredSixtySixFH_467
      · exact prime_oneHundredSixtySixFH_509
      · exact prime_oneHundredSixtySixFH_3303345043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 15564532260361971239) ^ 7782266130180985619 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 15564532260361971239) ^ 1414957478214724658 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 15564532260361971239) ^ 915560721197763014 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 15564532260361971239) ^ 293670420006829646 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 15564532260361971239) ^ 33328762870154114 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 15564532260361971239) ^ 30578648841575582 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 15564532260361971239) ^ 4711748866 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_16644054374457931199 : Nat.Prime 16644054374457931199 := by
  apply lucas_primality 16644054374457931199 (7 : ZMod 16644054374457931199)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (67, 1), (7109, 1), (296137769987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (67, 1), (7109, 1), (296137769987, 1)] : List FactorBlock).map factorBlockValue).prod) = 16644054374457931199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_59
      · exact prime_oneHundredSixtySixFH_67
      · exact prime_oneHundredSixtySixFH_7109
      · exact prime_oneHundredSixtySixFH_296137769987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16644054374457931199) ^ 8322027187228965599 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 16644054374457931199) ^ 282102616516236122 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 16644054374457931199) ^ 248418722006834794 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 16644054374457931199) ^ 2341265209517222 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 16644054374457931199) ^ 56203754 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_18715588337908483487 : Nat.Prime 18715588337908483487 := by
  apply lucas_primality 18715588337908483487 (5 : ZMod 18715588337908483487)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (80037151, 1), (4031659717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (80037151, 1), (4031659717, 1)] : List FactorBlock).map factorBlockValue).prod) = 18715588337908483487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_29
      · exact prime_oneHundredSixtySixFH_80037151
      · exact prime_oneHundredSixtySixFH_4031659717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18715588337908483487) ^ 9357794168954241743 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 18715588337908483487) ^ 645365115100292534 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 18715588337908483487) ^ 233836263586 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 18715588337908483487) ^ 4642154758 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_26107539572420644691 : Nat.Prime 26107539572420644691 := by
  apply lucas_primality 26107539572420644691 (2 : ZMod 26107539572420644691)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (237341268840187679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (237341268840187679, 1)] : List FactorBlock).map factorBlockValue).prod) = 26107539572420644691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_237341268840187679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26107539572420644691) ^ 13053769786210322345 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26107539572420644691) ^ 5221507914484128938 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26107539572420644691) ^ 2373412688401876790 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 26107539572420644691) ^ 110 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_42961034736541709423 : Nat.Prime 42961034736541709423 := by
  apply lucas_primality 42961034736541709423 (5 : ZMod 42961034736541709423)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3240529, 1), (6628707031559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3240529, 1), (6628707031559, 1)] : List FactorBlock).map factorBlockValue).prod) = 42961034736541709423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3240529
      · exact prime_oneHundredSixtySixFH_6628707031559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 42961034736541709423) ^ 21480517368270854711 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 42961034736541709423) ^ 13257414063118 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 42961034736541709423) ^ 6481058 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_57806493343951883513 : Nat.Prime 57806493343951883513 := by
  apply lucas_primality 57806493343951883513 (3 : ZMod 57806493343951883513)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (977, 1), (769151, 1), (9615690257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (977, 1), (769151, 1), (9615690257, 1)] : List FactorBlock).map factorBlockValue).prod) = 57806493343951883513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_977
      · exact prime_oneHundredSixtySixFH_769151
      · exact prime_oneHundredSixtySixFH_9615690257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57806493343951883513) ^ 28903246671975941756 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 57806493343951883513) ^ 59167342214894456 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 57806493343951883513) ^ 75156235048712 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 57806493343951883513) ^ 6011684216 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_94688478763283473373 : Nat.Prime 94688478763283473373 := by
  apply lucas_primality 94688478763283473373 (2 : ZMod 94688478763283473373)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (647, 1), (134741, 1), (271539554509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (647, 1), (134741, 1), (271539554509, 1)] : List FactorBlock).map factorBlockValue).prod) = 94688478763283473373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_647
      · exact prime_oneHundredSixtySixFH_134741
      · exact prime_oneHundredSixtySixFH_271539554509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94688478763283473373) ^ 47344239381641736686 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94688478763283473373) ^ 146350044456388676 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94688478763283473373) ^ 702744367069292 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 94688478763283473373) ^ 348709708 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_367410403679106078191 : Nat.Prime 367410403679106078191 := by
  apply lucas_primality 367410403679106078191 (17 : ZMod 367410403679106078191)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (383, 1), (10704709, 1), (8961440177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (383, 1), (10704709, 1), (8961440177, 1)] : List FactorBlock).map factorBlockValue).prod) = 367410403679106078191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_383
      · exact prime_oneHundredSixtySixFH_10704709
      · exact prime_oneHundredSixtySixFH_8961440177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 367410403679106078191) ^ 183705201839553039095 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 367410403679106078191) ^ 73482080735821215638 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 367410403679106078191) ^ 959296093156934930 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 367410403679106078191) ^ 34322315877910 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 367410403679106078191) ^ 40999035470 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_484872133728911038367 : Nat.Prime 484872133728911038367 := by
  apply lucas_primality 484872133728911038367 (5 : ZMod 484872133728911038367)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (3221, 1), (11746151, 1), (337254167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (3221, 1), (11746151, 1), (337254167, 1)] : List FactorBlock).map factorBlockValue).prod) = 484872133728911038367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_3221
      · exact prime_oneHundredSixtySixFH_11746151
      · exact prime_oneHundredSixtySixFH_337254167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 484872133728911038367) ^ 242436066864455519183 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 484872133728911038367) ^ 25519585985732159914 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 484872133728911038367) ^ 150534658096526246 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 484872133728911038367) ^ 41279235532466 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 484872133728911038367) ^ 1437705390098 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1702070351494369974647 : Nat.Prime 1702070351494369974647 := by
  apply lucas_primality 1702070351494369974647 (5 : ZMod 1702070351494369974647)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (281, 1), (521, 1), (22271, 1), (261013968613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (281, 1), (521, 1), (22271, 1), (261013968613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1702070351494369974647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_281
      · exact prime_oneHundredSixtySixFH_521
      · exact prime_oneHundredSixtySixFH_22271
      · exact prime_oneHundredSixtySixFH_261013968613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1702070351494369974647) ^ 851035175747184987323 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1702070351494369974647) ^ 6057189862969288166 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1702070351494369974647) ^ 3266929657378829126 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1702070351494369974647) ^ 76425412037823626 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1702070351494369974647) ^ 6520993342 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1854494493661243948973 : Nat.Prime 1854494493661243948973 := by
  apply lucas_primality 1854494493661243948973 (2 : ZMod 1854494493661243948973)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (103, 1), (131, 1), (1279, 1), (1413946219451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (103, 1), (131, 1), (1279, 1), (1413946219451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1854494493661243948973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_103
      · exact prime_oneHundredSixtySixFH_131
      · exact prime_oneHundredSixtySixFH_1279
      · exact prime_oneHundredSixtySixFH_1413946219451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1854494493661243948973) ^ 927247246830621974486 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1854494493661243948973) ^ 97604973350591786788 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1854494493661243948973) ^ 18004800909332465524 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1854494493661243948973) ^ 14156446516498045412 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1854494493661243948973) ^ 1449956601767978068 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1854494493661243948973) ^ 1311573572 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_2397677616984963445807 : Nat.Prime 2397677616984963445807 := by
  apply lucas_primality 2397677616984963445807 (3 : ZMod 2397677616984963445807)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139787, 1), (2858727465101623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139787, 1), (2858727465101623, 1)] : List FactorBlock).map factorBlockValue).prod) = 2397677616984963445807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_139787
      · exact prime_oneHundredSixtySixFH_2858727465101623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2397677616984963445807) ^ 1198838808492481722903 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2397677616984963445807) ^ 799225872328321148602 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2397677616984963445807) ^ 17152364790609738 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2397677616984963445807) ^ 838722 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_2777015370786200554079 : Nat.Prime 2777015370786200554079 := by
  apply lucas_primality 2777015370786200554079 (11 : ZMod 2777015370786200554079)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (421, 1), (811519, 1), (4064129142461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (421, 1), (811519, 1), (4064129142461, 1)] : List FactorBlock).map factorBlockValue).prod) = 2777015370786200554079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_421
      · exact prime_oneHundredSixtySixFH_811519
      · exact prime_oneHundredSixtySixFH_4064129142461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2777015370786200554079) ^ 1388507685393100277039 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2777015370786200554079) ^ 6596236035121616518 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2777015370786200554079) ^ 3421996737952162 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2777015370786200554079) ^ 683298998 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_3425082146295901310381 : Nat.Prime 3425082146295901310381 := by
  apply lucas_primality 3425082146295901310381 (3 : ZMod 3425082146295901310381)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (31, 1), (163, 1), (797, 1), (840439, 1), (7228183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (31, 1), (163, 1), (797, 1), (840439, 1), (7228183, 1)] : List FactorBlock).map factorBlockValue).prod) = 3425082146295901310381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_31
      · exact prime_oneHundredSixtySixFH_163
      · exact prime_oneHundredSixtySixFH_797
      · exact prime_oneHundredSixtySixFH_840439
      · exact prime_oneHundredSixtySixFH_7228183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3425082146295901310381) ^ 1712541073147950655190 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3425082146295901310381) ^ 685016429259180262076 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3425082146295901310381) ^ 489297449470843044340 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3425082146295901310381) ^ 110486520848254880980 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3425082146295901310381) ^ 21012773903655836260 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3425082146295901310381) ^ 4297468188577040540 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3425082146295901310381) ^ 4075348890634420 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3425082146295901310381) ^ 473851055831860 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_5408881132349583101431 : Nat.Prime 5408881132349583101431 := by
  apply lucas_primality 5408881132349583101431 (6 : ZMod 5408881132349583101431)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (7, 1), (317982429885337043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (7, 1), (317982429885337043, 1)] : List FactorBlock).map factorBlockValue).prod) = 5408881132349583101431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_317982429885337043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5408881132349583101431) ^ 2704440566174791550715 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 5408881132349583101431) ^ 1802960377449861033810 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 5408881132349583101431) ^ 1081776226469916620286 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 5408881132349583101431) ^ 772697304621369014490 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 5408881132349583101431) ^ 17010 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_5872439941861824832609 : Nat.Prime 5872439941861824832609 := by
  apply lucas_primality 5872439941861824832609 (7 : ZMod 5872439941861824832609)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (571, 1), (35710011321887921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (571, 1), (35710011321887921, 1)] : List FactorBlock).map factorBlockValue).prod) = 5872439941861824832609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_571
      · exact prime_oneHundredSixtySixFH_35710011321887921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5872439941861824832609) ^ 2936219970930912416304 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 5872439941861824832609) ^ 1957479980620608277536 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 5872439941861824832609) ^ 10284483260703721248 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 5872439941861824832609) ^ 164448 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_7531573462721617269007 : Nat.Prime 7531573462721617269007 := by
  apply lucas_primality 7531573462721617269007 (3 : ZMod 7531573462721617269007)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (41, 1), (215317, 1), (1003609, 1), (15742193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (41, 1), (215317, 1), (1003609, 1), (15742193, 1)] : List FactorBlock).map factorBlockValue).prod) = 7531573462721617269007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_41
      · exact prime_oneHundredSixtySixFH_215317
      · exact prime_oneHundredSixtySixFH_1003609
      · exact prime_oneHundredSixtySixFH_15742193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7531573462721617269007) ^ 3765786731360808634503 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7531573462721617269007) ^ 2510524487573872423002 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7531573462721617269007) ^ 183696913724917494366 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7531573462721617269007) ^ 34979000556024918 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7531573462721617269007) ^ 7504489759180734 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7531573462721617269007) ^ 478432291023342 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_9956704452447978103913 : Nat.Prime 9956704452447978103913 := by
  apply lucas_primality 9956704452447978103913 (3 : ZMod 9956704452447978103913)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (193, 1), (617, 1), (950146276717679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (193, 1), (617, 1), (950146276717679, 1)] : List FactorBlock).map factorBlockValue).prod) = 9956704452447978103913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_193
      · exact prime_oneHundredSixtySixFH_617
      · exact prime_oneHundredSixtySixFH_950146276717679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9956704452447978103913) ^ 4978352226223989051956 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9956704452447978103913) ^ 905154950222543463992 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9956704452447978103913) ^ 51589142240663098984 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9956704452447978103913) ^ 16137284363773060136 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9956704452447978103913) ^ 10479128 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_12337837474505881421183 : Nat.Prime 12337837474505881421183 := by
  apply lucas_primality 12337837474505881421183 (5 : ZMod 12337837474505881421183)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (61, 1), (19013, 1), (43958533532647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (61, 1), (19013, 1), (43958533532647, 1)] : List FactorBlock).map factorBlockValue).prod) = 12337837474505881421183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_61
      · exact prime_oneHundredSixtySixFH_19013
      · exact prime_oneHundredSixtySixFH_43958533532647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12337837474505881421183) ^ 6168918737252940710591 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12337837474505881421183) ^ 1121621588591443765562 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12337837474505881421183) ^ 202259630729604613462 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12337837474505881421183) ^ 648915872008935014 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12337837474505881421183) ^ 280669906 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_24228150214036459567619 : Nat.Prime 24228150214036459567619 := by
  apply lucas_primality 24228150214036459567619 (2 : ZMod 24228150214036459567619)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (157, 1), (239, 1), (46120570267448269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (157, 1), (239, 1), (46120570267448269, 1)] : List FactorBlock).map factorBlockValue).prod) = 24228150214036459567619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_157
      · exact prime_oneHundredSixtySixFH_239
      · exact prime_oneHundredSixtySixFH_46120570267448269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24228150214036459567619) ^ 12114075107018229783809 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24228150214036459567619) ^ 3461164316290922795374 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24228150214036459567619) ^ 154319428114881908074 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24228150214036459567619) ^ 101373013447851295262 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 24228150214036459567619) ^ 525322 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_29541958961262594513077 : Nat.Prime 29541958961262594513077 := by
  apply lucas_primality 29541958961262594513077 (2 : ZMod 29541958961262594513077)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (4253, 1), (13799, 1), (306853, 1), (24124427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (4253, 1), (13799, 1), (306853, 1), (24124427, 1)] : List FactorBlock).map factorBlockValue).prod) = 29541958961262594513077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_4253
      · exact prime_oneHundredSixtySixFH_13799
      · exact prime_oneHundredSixtySixFH_306853
      · exact prime_oneHundredSixtySixFH_24124427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29541958961262594513077) ^ 14770979480631297256538 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 29541958961262594513077) ^ 1737762291838976147828 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 29541958961262594513077) ^ 6946146005469690692 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 29541958961262594513077) ^ 2140876799859598124 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 29541958961262594513077) ^ 96273977967504292 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 29541958961262594513077) ^ 1224566244050588 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_71945204904752565187369 : Nat.Prime 71945204904752565187369 := by
  apply lucas_primality 71945204904752565187369 (11 : ZMod 71945204904752565187369)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (37, 1), (1213, 1), (110603, 1), (9585629323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (37, 1), (1213, 1), (110603, 1), (9585629323, 1)] : List FactorBlock).map factorBlockValue).prod) = 71945204904752565187369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_37
      · exact prime_oneHundredSixtySixFH_1213
      · exact prime_oneHundredSixtySixFH_110603
      · exact prime_oneHundredSixtySixFH_9585629323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 71945204904752565187369) ^ 35972602452376282593684 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71945204904752565187369) ^ 23981734968250855062456 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71945204904752565187369) ^ 10277886414964652169624 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71945204904752565187369) ^ 1944464997425745005064 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71945204904752565187369) ^ 59311792996498404936 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71945204904752565187369) ^ 650481496024091256 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (11 : ZMod 71945204904752565187369) ^ 7505527543416 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_108820892253348261675697 : Nat.Prime 108820892253348261675697 := by
  apply lucas_primality 108820892253348261675697 (15 : ZMod 108820892253348261675697)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (827354377, 1), (391454631943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (827354377, 1), (391454631943, 1)] : List FactorBlock).map factorBlockValue).prod) = 108820892253348261675697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_827354377
      · exact prime_oneHundredSixtySixFH_391454631943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 108820892253348261675697) ^ 54410446126674130837848 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (15 : ZMod 108820892253348261675697) ^ 36273630751116087225232 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (15 : ZMod 108820892253348261675697) ^ 15545841750478323096528 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (15 : ZMod 108820892253348261675697) ^ 131528756332848 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (15 : ZMod 108820892253348261675697) ^ 277991070672 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_120888492808254846913507 : Nat.Prime 120888492808254846913507 := by
  apply lucas_primality 120888492808254846913507 (2 : ZMod 120888492808254846913507)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (304433, 1), (20037197, 1), (113895619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (304433, 1), (20037197, 1), (113895619, 1)] : List FactorBlock).map factorBlockValue).prod) = 120888492808254846913507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_29
      · exact prime_oneHundredSixtySixFH_304433
      · exact prime_oneHundredSixtySixFH_20037197
      · exact prime_oneHundredSixtySixFH_113895619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 120888492808254846913507) ^ 60444246404127423456753 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 120888492808254846913507) ^ 40296164269418282304502 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 120888492808254846913507) ^ 4168568717526029203914 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 120888492808254846913507) ^ 397093918229150082 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 120888492808254846913507) ^ 6033203786350698 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 120888492808254846913507) ^ 1061397215008374 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_132563870268596862722201 : Nat.Prime 132563870268596862722201 := by
  apply lucas_primality 132563870268596862722201 (3 : ZMod 132563870268596862722201)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7, 1), (94688478763283473373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7, 1), (94688478763283473373, 1)] : List FactorBlock).map factorBlockValue).prod) = 132563870268596862722201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_94688478763283473373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 132563870268596862722201) ^ 66281935134298431361100 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 132563870268596862722201) ^ 26512774053719372544440 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 132563870268596862722201) ^ 18937695752656694674600 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 132563870268596862722201) ^ 1400 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_136693864861693600332433 : Nat.Prime 136693864861693600332433 := by
  apply lucas_primality 136693864861693600332433 (5 : ZMod 136693864861693600332433)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (53, 1), (19717, 1), (247741289789569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (53, 1), (19717, 1), (247741289789569, 1)] : List FactorBlock).map factorBlockValue).prod) = 136693864861693600332433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_53
      · exact prime_oneHundredSixtySixFH_19717
      · exact prime_oneHundredSixtySixFH_247741289789569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 136693864861693600332433) ^ 68346932430846800166216 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 136693864861693600332433) ^ 45564621620564533444144 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 136693864861693600332433) ^ 12426714987426690939312 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 136693864861693600332433) ^ 2579129525692332081744 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 136693864861693600332433) ^ 6932792253471298896 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 136693864861693600332433) ^ 551760528 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_144375745036626875144839 : Nat.Prime 144375745036626875144839 := by
  apply lucas_primality 144375745036626875144839 (6 : ZMod 144375745036626875144839)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (64739617, 1), (21863714157457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (64739617, 1), (21863714157457, 1)] : List FactorBlock).map factorBlockValue).prod) = 144375745036626875144839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_64739617
      · exact prime_oneHundredSixtySixFH_21863714157457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 144375745036626875144839) ^ 72187872518313437572419 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 144375745036626875144839) ^ 48125248345542291714946 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 144375745036626875144839) ^ 8492690884507463243814 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 144375745036626875144839) ^ 2230098844060614 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 144375745036626875144839) ^ 6603440934 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_148054049694070577054197 : Nat.Prime 148054049694070577054197 := by
  apply lucas_primality 148054049694070577054197 (2 : ZMod 148054049694070577054197)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (12337837474505881421183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (12337837474505881421183, 1)] : List FactorBlock).map factorBlockValue).prod) = 148054049694070577054197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_12337837474505881421183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 148054049694070577054197) ^ 74027024847035288527098 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 148054049694070577054197) ^ 49351349898023525684732 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 148054049694070577054197) ^ 12 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_191473486540766711285681 : Nat.Prime 191473486540766711285681 := by
  apply lucas_primality 191473486540766711285681 (3 : ZMod 191473486540766711285681)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 1), (103, 1), (1831, 1), (1729157, 1), (564566767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 1), (103, 1), (1831, 1), (1729157, 1), (564566767, 1)] : List FactorBlock).map factorBlockValue).prod) = 191473486540766711285681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_103
      · exact prime_oneHundredSixtySixFH_1831
      · exact prime_oneHundredSixtySixFH_1729157
      · exact prime_oneHundredSixtySixFH_564566767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 191473486540766711285681) ^ 95736743270383355642840 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 191473486540766711285681) ^ 38294697308153342257136 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 191473486540766711285681) ^ 14728729733905131637360 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 191473486540766711285681) ^ 1858965888745307876560 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 191473486540766711285681) ^ 104573176701674883280 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 191473486540766711285681) ^ 110732273900384240 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 191473486540766711285681) ^ 339151182345040 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_259211524023769459017347 : Nat.Prime 259211524023769459017347 := by
  apply lucas_primality 259211524023769459017347 (2 : ZMod 259211524023769459017347)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (87877, 1), (77623904950810271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (87877, 1), (77623904950810271, 1)] : List FactorBlock).map factorBlockValue).prod) = 259211524023769459017347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_87877
      · exact prime_oneHundredSixtySixFH_77623904950810271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 259211524023769459017347) ^ 129605762011884729508673 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 259211524023769459017347) ^ 13642711790724708369334 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 259211524023769459017347) ^ 2949708388130790298 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 259211524023769459017347) ^ 3339326 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_294557064581447512692767 : Nat.Prime 294557064581447512692767 := by
  apply lucas_primality 294557064581447512692767 (5 : ZMod 294557064581447512692767)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (3425082146295901310381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (3425082146295901310381, 1)] : List FactorBlock).map factorBlockValue).prod) = 294557064581447512692767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_43
      · exact prime_oneHundredSixtySixFH_3425082146295901310381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 294557064581447512692767) ^ 147278532290723756346383 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 294557064581447512692767) ^ 6850164292591802620762 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 294557064581447512692767) ^ 86 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_373288970137971775442057 : Nat.Prime 373288970137971775442057 := by
  apply lucas_primality 373288970137971775442057 (3 : ZMod 373288970137971775442057)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (127, 1), (367410403679106078191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (127, 1), (367410403679106078191, 1)] : List FactorBlock).map factorBlockValue).prod) = 373288970137971775442057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_127
      · exact prime_oneHundredSixtySixFH_367410403679106078191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 373288970137971775442057) ^ 186644485068985887721028 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 373288970137971775442057) ^ 2939283229432848625528 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 373288970137971775442057) ^ 1016 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_601080233628382090886189 : Nat.Prime 601080233628382090886189 := by
  apply lucas_primality 601080233628382090886189 (2 : ZMod 601080233628382090886189)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2069, 1), (7369, 1), (9856061574361127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2069, 1), (7369, 1), (9856061574361127, 1)] : List FactorBlock).map factorBlockValue).prod) = 601080233628382090886189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_2069
      · exact prime_oneHundredSixtySixFH_7369
      · exact prime_oneHundredSixtySixFH_9856061574361127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 601080233628382090886189) ^ 300540116814191045443094 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 601080233628382090886189) ^ 290517270965868579452 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 601080233628382090886189) ^ 81568765589412687052 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 601080233628382090886189) ^ 60985844 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_688188790022612273621689 : Nat.Prime 688188790022612273621689 := by
  apply lucas_primality 688188790022612273621689 (17 : ZMod 688188790022612273621689)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (47, 1), (7923330455266329023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (47, 1), (7923330455266329023, 1)] : List FactorBlock).map factorBlockValue).prod) = 688188790022612273621689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_47
      · exact prime_oneHundredSixtySixFH_7923330455266329023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 688188790022612273621689) ^ 344094395011306136810844 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 688188790022612273621689) ^ 229396263340870757873896 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 688188790022612273621689) ^ 98312684288944610517384 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 688188790022612273621689) ^ 62562617274782933965608 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 688188790022612273621689) ^ 14642314681332176034504 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (17 : ZMod 688188790022612273621689) ^ 86856 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1003016889807470500582043 : Nat.Prime 1003016889807470500582043 := by
  apply lucas_primality 1003016889807470500582043 (2 : ZMod 1003016889807470500582043)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20641, 1), (190025999, 1), (127859938819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20641, 1), (190025999, 1), (127859938819, 1)] : List FactorBlock).map factorBlockValue).prod) = 1003016889807470500582043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_20641
      · exact prime_oneHundredSixtySixFH_190025999
      · exact prime_oneHundredSixtySixFH_127859938819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1003016889807470500582043) ^ 501508444903735250291021 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1003016889807470500582043) ^ 48593425212318710362 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1003016889807470500582043) ^ 5278313994325958 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1003016889807470500582043) ^ 7844653290718 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1555269144142616754104083 : Nat.Prime 1555269144142616754104083 := by
  apply lucas_primality 1555269144142616754104083 (3 : ZMod 1555269144142616754104083)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (259211524023769459017347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (259211524023769459017347, 1)] : List FactorBlock).map factorBlockValue).prod) = 1555269144142616754104083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_259211524023769459017347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1555269144142616754104083) ^ 777634572071308377052041 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1555269144142616754104083) ^ 518423048047538918034694 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1555269144142616754104083) ^ 6 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_23029371363655071927585781 : Nat.Prime 23029371363655071927585781 := by
  apply lucas_primality 23029371363655071927585781 (2 : ZMod 23029371363655071927585781)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (433, 1), (7448965708481337269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (433, 1), (7448965708481337269, 1)] : List FactorBlock).map factorBlockValue).prod) = 23029371363655071927585781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_17
      · exact prime_oneHundredSixtySixFH_433
      · exact prime_oneHundredSixtySixFH_7448965708481337269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23029371363655071927585781) ^ 11514685681827535963792890 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23029371363655071927585781) ^ 7676457121218357309195260 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23029371363655071927585781) ^ 4605874272731014385517156 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23029371363655071927585781) ^ 3289910194807867418226540 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23029371363655071927585781) ^ 1354668903744415995740340 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23029371363655071927585781) ^ 53185615158556748100660 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 23029371363655071927585781) ^ 3091620 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_39970733759891756205068437 : Nat.Prime 39970733759891756205068437 := by
  apply lucas_primality 39970733759891756205068437 (5 : ZMod 39970733759891756205068437)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2673577, 1), (3506549, 1), (355294321411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2673577, 1), (3506549, 1), (355294321411, 1)] : List FactorBlock).map factorBlockValue).prod) = 39970733759891756205068437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_2673577
      · exact prime_oneHundredSixtySixFH_3506549
      · exact prime_oneHundredSixtySixFH_355294321411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 39970733759891756205068437) ^ 19985366879945878102534218 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 39970733759891756205068437) ^ 13323577919963918735022812 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 39970733759891756205068437) ^ 14950283369393047668 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 39970733759891756205068437) ^ 11398880711460685764 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (5 : ZMod 39970733759891756205068437) ^ 112500345069276 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_52460920278286159574147561 : Nat.Prime 52460920278286159574147561 := by
  apply lucas_primality 52460920278286159574147561 (3 : ZMod 52460920278286159574147561)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29, 1), (41, 1), (607, 1), (186178393, 1), (9760590451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29, 1), (41, 1), (607, 1), (186178393, 1), (9760590451, 1)] : List FactorBlock).map factorBlockValue).prod) = 52460920278286159574147561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_29
      · exact prime_oneHundredSixtySixFH_41
      · exact prime_oneHundredSixtySixFH_607
      · exact prime_oneHundredSixtySixFH_186178393
      · exact prime_oneHundredSixtySixFH_9760590451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52460920278286159574147561) ^ 26230460139143079787073780 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 52460920278286159574147561) ^ 10492184055657231914829512 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 52460920278286159574147561) ^ 1808997250975384812901640 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 52460920278286159574147561) ^ 1279534640933808770101160 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 52460920278286159574147561) ^ 86426557295364348557080 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 52460920278286159574147561) ^ 281777704882682920 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 52460920278286159574147561) ^ 5374769133245560 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_228470666776564054676235187 : Nat.Prime 228470666776564054676235187 := by
  apply lucas_primality 228470666776564054676235187 (2 : ZMod 228470666776564054676235187)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4493, 1), (41737, 1), (203058676328107591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4493, 1), (41737, 1), (203058676328107591, 1)] : List FactorBlock).map factorBlockValue).prod) = 228470666776564054676235187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_4493
      · exact prime_oneHundredSixtySixFH_41737
      · exact prime_oneHundredSixtySixFH_203058676328107591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 228470666776564054676235187) ^ 114235333388282027338117593 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 228470666776564054676235187) ^ 76156888925521351558745062 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 228470666776564054676235187) ^ 50850359843437359153402 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 228470666776564054676235187) ^ 5474055796453124438178 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 228470666776564054676235187) ^ 1125146046 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_326007147443635420210774129 : Nat.Prime 326007147443635420210774129 := by
  apply lucas_primality 326007147443635420210774129 (7 : ZMod 326007147443635420210774129)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (23, 1), (97883, 1), (274257234013327139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (23, 1), (97883, 1), (274257234013327139, 1)] : List FactorBlock).map factorBlockValue).prod) = 326007147443635420210774129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_23
      · exact prime_oneHundredSixtySixFH_97883
      · exact prime_oneHundredSixtySixFH_274257234013327139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 326007147443635420210774129) ^ 163003573721817710105387064 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 326007147443635420210774129) ^ 108669049147878473403591376 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 326007147443635420210774129) ^ 29637013403966856382797648 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 326007147443635420210774129) ^ 14174223801897192183077136 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 326007147443635420210774129) ^ 3330579849857844776016 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 326007147443635420210774129) ^ 1188691152 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_360103307818474354067680781 : Nat.Prime 360103307818474354067680781 := by
  apply lucas_primality 360103307818474354067680781 (7 : ZMod 360103307818474354067680781)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 2), (3764149, 1), (26854979, 1), (1472041729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 2), (3764149, 1), (26854979, 1), (1472041729, 1)] : List FactorBlock).map factorBlockValue).prod) = 360103307818474354067680781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_3764149
      · exact prime_oneHundredSixtySixFH_26854979
      · exact prime_oneHundredSixtySixFH_1472041729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 360103307818474354067680781) ^ 180051653909237177033840390 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 360103307818474354067680781) ^ 72020661563694870813536156 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 360103307818474354067680781) ^ 32736664347134032187970980 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 360103307818474354067680781) ^ 95666592320993232220 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 360103307818474354067680781) ^ 13409182253260162820 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 360103307818474354067680781) ^ 244628464481847820 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_1869107645343509742541771673 : Nat.Prime 1869107645343509742541771673 := by
  apply lucas_primality 1869107645343509742541771673 (3 : ZMod 1869107645343509742541771673)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (113, 1), (108820892253348261675697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (113, 1), (108820892253348261675697, 1)] : List FactorBlock).map factorBlockValue).prod) = 1869107645343509742541771673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_19
      · exact prime_oneHundredSixtySixFH_113
      · exact prime_oneHundredSixtySixFH_108820892253348261675697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1869107645343509742541771673) ^ 934553822671754871270885836 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1869107645343509742541771673) ^ 98374086597026828554830088 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1869107645343509742541771673) ^ 16540775622508935774705944 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1869107645343509742541771673) ^ 17176 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_4175666016192947297167787779 : Nat.Prime 4175666016192947297167787779 := by
  apply lucas_primality 4175666016192947297167787779 (2 : ZMod 4175666016192947297167787779)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2083, 1), (52237, 1), (77743973, 1), (82269768761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2083, 1), (52237, 1), (77743973, 1), (82269768761, 1)] : List FactorBlock).map factorBlockValue).prod) = 4175666016192947297167787779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_2083
      · exact prime_oneHundredSixtySixFH_52237
      · exact prime_oneHundredSixtySixFH_77743973
      · exact prime_oneHundredSixtySixFH_82269768761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4175666016192947297167787779) ^ 2087833008096473648583893889 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4175666016192947297167787779) ^ 1391888672064315765722595926 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4175666016192947297167787779) ^ 2004640430241453335174166 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4175666016192947297167787779) ^ 79936941558530300307594 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4175666016192947297167787779) ^ 53710478832782925786 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4175666016192947297167787779) ^ 50755776746177298 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_4460370517297011885611046037 : Nat.Prime 4460370517297011885611046037 := by
  apply lucas_primality 4460370517297011885611046037 (2 : ZMod 4460370517297011885611046037)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (191, 1), (376654387, 1), (469700051604569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (191, 1), (376654387, 1), (469700051604569, 1)] : List FactorBlock).map factorBlockValue).prod) = 4460370517297011885611046037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_191
      · exact prime_oneHundredSixtySixFH_376654387
      · exact prime_oneHundredSixtySixFH_469700051604569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4460370517297011885611046037) ^ 2230185258648505942805523018 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4460370517297011885611046037) ^ 1486790172432337295203682012 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4460370517297011885611046037) ^ 405488228845182898691913276 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4460370517297011885611046037) ^ 23352725221450324008434796 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4460370517297011885611046037) ^ 11842077701054393628 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4460370517297011885611046037) ^ 9496210405044 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_4786739091733378608948439651 : Nat.Prime 4786739091733378608948439651 := by
  apply lucas_primality 4786739091733378608948439651 (3 : ZMod 4786739091733378608948439651)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (31, 1), (232554011, 1), (402411407710181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (31, 1), (232554011, 1), (402411407710181, 1)] : List FactorBlock).map factorBlockValue).prod) = 4786739091733378608948439651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_11
      · exact prime_oneHundredSixtySixFH_31
      · exact prime_oneHundredSixtySixFH_232554011
      · exact prime_oneHundredSixtySixFH_402411407710181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4786739091733378608948439651) ^ 2393369545866689304474219825 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4786739091733378608948439651) ^ 1595579697244459536316146550 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4786739091733378608948439651) ^ 957347818346675721789687930 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4786739091733378608948439651) ^ 435158099248488964449858150 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4786739091733378608948439651) ^ 154410938443012213191885150 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4786739091733378608948439651) ^ 20583343504375758150 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4786739091733378608948439651) ^ 11895137662650 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_15096638673928347920529694277 : Nat.Prime 15096638673928347920529694277 := by
  apply lucas_primality 15096638673928347920529694277 (2 : ZMod 15096638673928347920529694277)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (31, 1), (44542537229, 1), (30036009397841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (31, 1), (44542537229, 1), (30036009397841, 1)] : List FactorBlock).map factorBlockValue).prod) = 15096638673928347920529694277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_13
      · exact prime_oneHundredSixtySixFH_31
      · exact prime_oneHundredSixtySixFH_44542537229
      · exact prime_oneHundredSixtySixFH_30036009397841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15096638673928347920529694277) ^ 7548319336964173960264847138 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15096638673928347920529694277) ^ 2156662667704049702932813468 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15096638673928347920529694277) ^ 1161279897994488301579207252 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15096638673928347920529694277) ^ 486988344320269287759022396 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15096638673928347920529694277) ^ 338926330045237844 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 15096638673928347920529694277) ^ 502617990092036 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_28036614680152646138126575091 : Nat.Prime 28036614680152646138126575091 := by
  apply lucas_primality 28036614680152646138126575091 (2 : ZMod 28036614680152646138126575091)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1373897855507, 1), (2040662234661287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1373897855507, 1), (2040662234661287, 1)] : List FactorBlock).map factorBlockValue).prod) = 28036614680152646138126575091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_1373897855507
      · exact prime_oneHundredSixtySixFH_2040662234661287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28036614680152646138126575091) ^ 14018307340076323069063287545 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 28036614680152646138126575091) ^ 5607322936030529227625315018 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 28036614680152646138126575091) ^ 20406622346612870 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 28036614680152646138126575091) ^ 13738978555070 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_49064075690267130741721506403 : Nat.Prime 49064075690267130741721506403 := by
  apply lucas_primality 49064075690267130741721506403 (2 : ZMod 49064075690267130741721506403)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (23, 1), (3000898489, 1), (13164086306799229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (23, 1), (3000898489, 1), (13164086306799229, 1)] : List FactorBlock).map factorBlockValue).prod) = 49064075690267130741721506403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_23
      · exact prime_oneHundredSixtySixFH_3000898489
      · exact prime_oneHundredSixtySixFH_13164086306799229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49064075690267130741721506403) ^ 24532037845133565370860753201 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 49064075690267130741721506403) ^ 16354691896755710247240502134 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 49064075690267130741721506403) ^ 2133220682185527423553108974 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 49064075690267130741721506403) ^ 16349795193044642418 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 49064075690267130741721506403) ^ 3727115923338 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_65418767587022840988962008549 : Nat.Prime 65418767587022840988962008549 := by
  apply lucas_primality 65418767587022840988962008549 (2 : ZMod 65418767587022840988962008549)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (10639, 1), (660659, 1), (110801313211341497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (10639, 1), (660659, 1), (110801313211341497, 1)] : List FactorBlock).map factorBlockValue).prod) = 65418767587022840988962008549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_10639
      · exact prime_oneHundredSixtySixFH_660659
      · exact prime_oneHundredSixtySixFH_110801313211341497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65418767587022840988962008549) ^ 32709383793511420494481004274 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 65418767587022840988962008549) ^ 21806255862340946996320669516 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 65418767587022840988962008549) ^ 9345538226717548712708858364 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 65418767587022840988962008549) ^ 6148958321930899613587932 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 65418767587022840988962008549) ^ 99020474385458823672972 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (2 : ZMod 65418767587022840988962008549) ^ 590415092484 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_98128151380534261483443012823 : Nat.Prime 98128151380534261483443012823 := by
  apply lucas_primality 98128151380534261483443012823 (6 : ZMod 98128151380534261483443012823)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (10639, 1), (660659, 1), (110801313211341497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (10639, 1), (660659, 1), (110801313211341497, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534261483443012823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_7
      · exact prime_oneHundredSixtySixFH_10639
      · exact prime_oneHundredSixtySixFH_660659
      · exact prime_oneHundredSixtySixFH_110801313211341497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 98128151380534261483443012823) ^ 49064075690267130741721506411 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 98128151380534261483443012823) ^ 32709383793511420494481004274 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 98128151380534261483443012823) ^ 14018307340076323069063287546 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 98128151380534261483443012823) ^ 9223437482896349420381898 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 98128151380534261483443012823) ^ 148530711578188235509458 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 98128151380534261483443012823) ^ 885622638726 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_196256302761068522966886025621 : Nat.Prime 196256302761068522966886025621 := by
  apply lucas_primality 196256302761068522966886025621 (6 : ZMod 196256302761068522966886025621)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (263, 1), (7307, 1), (1702070351494369974647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (263, 1), (7307, 1), (1702070351494369974647, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_5
      · exact prime_oneHundredSixtySixFH_263
      · exact prime_oneHundredSixtySixFH_7307
      · exact prime_oneHundredSixtySixFH_1702070351494369974647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 196256302761068522966886025621) ^ 98128151380534261483443012810 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 196256302761068522966886025621) ^ 65418767587022840988962008540 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 196256302761068522966886025621) ^ 39251260552213704593377205124 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 196256302761068522966886025621) ^ 746221683502161684284737740 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 196256302761068522966886025621) ^ 26858670146581158199929660 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (6 : ZMod 196256302761068522966886025621) ^ 115304460 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtySixFH_196256302761068522966886025657 : Nat.Prime 196256302761068522966886025657 := by
  apply lucas_primality 196256302761068522966886025657 (7 : ZMod 196256302761068522966886025657)
  · rw [← oneHundredSixtySixFHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (140557, 1), (4272126527, 1), (13618077000271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (140557, 1), (4272126527, 1), (13618077000271, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtySixFH_2
      · exact prime_oneHundredSixtySixFH_3
      · exact prime_oneHundredSixtySixFH_140557
      · exact prime_oneHundredSixtySixFH_4272126527
      · exact prime_oneHundredSixtySixFH_13618077000271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 196256302761068522966886025657) ^ 98128151380534261483443012828 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 196256302761068522966886025657) ^ 65418767587022840988962008552 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 196256302761068522966886025657) ^ 1396275551990071806931608 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 196256302761068522966886025657) ^ 45938785174250182728 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide
    · change (7 : ZMod 196256302761068522966886025657) ^ 14411454918132936 ≠ 1
      rw [← oneHundredSixtySixFHFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025600 : Nat.totient 196256302761068522966886025600 = 77556254988779073670219776000 := by
  rw [← show ((([(2, 7), (5, 2), (83, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_83, prime_oneHundredSixtySixFH_171401, prime_oneHundredSixtySixFH_714027719, prime_oneHundredSixtySixFH_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025601 : Nat.totient 196256302761068522966886025601 = 181159664087140175046356331312 := by
  rw [← show ((([(13, 1), (15096638673928347920529694277, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_13, prime_oneHundredSixtySixFH_15096638673928347920529694277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025602 : Nat.totient 196256302761068522966886025602 = 55457666187140229328509250176 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (107, 1), (607, 1), (71945204904752565187369, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_107, prime_oneHundredSixtySixFH_607, prime_oneHundredSixtySixFH_71945204904752565187369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025603 : Nat.totient 196256302761068522966886025603 = 196155523176225258168312409728 := by
  rw [← show ((([(1949, 1), (2343889, 1), (42961034736541709423, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_1949, prime_oneHundredSixtySixFH_2343889, prime_oneHundredSixtySixFH_42961034736541709423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025604 : Nat.totient 196256302761068522966886025604 = 98125040842245976249934741544 := by
  rw [← show ((([(2, 2), (31547, 1), (1555269144142616754104083, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_31547, prime_oneHundredSixtySixFH_1555269144142616754104083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025605 : Nat.totient 196256302761068522966886025605 = 104670013303280596292331180608 := by
  rw [← show ((([(3, 1), (5, 1), (7055159, 1), (1854494493661243948973, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_7055159, prime_oneHundredSixtySixFH_1854494493661243948973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025606 : Nat.totient 196256302761068522966886025606 = 86534174476588156347796272000 := by
  rw [← show ((([(2, 1), (11, 1), (37, 1), (331, 1), (11158130381, 1), (65279945407739, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_11, prime_oneHundredSixtySixFH_37, prime_oneHundredSixtySixFH_331, prime_oneHundredSixtySixFH_11158130381, prime_oneHundredSixtySixFH_65279945407739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025607 : Nat.totient 196256302761068522966886025607 = 195733332638010126434003865600 := by
  rw [← show ((([(653, 1), (881, 1), (810849569, 1), (420721041685171, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_653, prime_oneHundredSixtySixFH_881, prime_oneHundredSixtySixFH_810849569, prime_oneHundredSixtySixFH_420721041685171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025608 : Nat.totient 196256302761068522966886025608 = 62574473323256886960831346176 := by
  rw [← show ((([(2, 3), (3, 3), (23, 1), (3000898489, 1), (13164086306799229, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_23, prime_oneHundredSixtySixFH_3000898489, prime_oneHundredSixtySixFH_13164086306799229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025609 : Nat.totient 196256302761068522966886025609 = 154461779982575858667257856000 := by
  rw [← show ((([(7, 1), (17, 1), (41, 1), (147073, 1), (13977427, 1), (19567376924701, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_17, prime_oneHundredSixtySixFH_41, prime_oneHundredSixtySixFH_147073, prime_oneHundredSixtySixFH_13977427, prime_oneHundredSixtySixFH_19567376924701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025610 : Nat.totient 196256302761068522966886025610 = 78141650308252884668348339328 := by
  rw [← show ((([(2, 1), (5, 1), (223, 1), (8839, 1), (9956704452447978103913, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_223, prime_oneHundredSixtySixFH_8839, prime_oneHundredSixtySixFH_9956704452447978103913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025611 : Nat.totient 196256302761068522966886025611 = 130705496049401632948765366080 := by
  rw [← show ((([(3, 1), (991, 1), (9785129, 1), (6746245607888531183, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_991, prime_oneHundredSixtySixFH_9785129, prime_oneHundredSixtySixFH_6746245607888531183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025612 : Nat.totient 196256302761068522966886025612 = 98128151380534261483443012804 := by
  rw [← show ((([(2, 2), (49064075690267130741721506403, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_49064075690267130741721506403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025613 : Nat.totient 196256302761068522966886025613 = 192080636744875575669718237788 := by
  rw [← show ((([(47, 1), (4175666016192947297167787779, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_47, prime_oneHundredSixtySixFH_4175666016192947297167787779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025614 : Nat.totient 196256302761068522966886025614 = 57641774919351277344050769408 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (29, 1), (157, 1), (199, 1), (2777015370786200554079, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_13, prime_oneHundredSixtySixFH_29, prime_oneHundredSixtySixFH_157, prime_oneHundredSixtySixFH_199, prime_oneHundredSixtySixFH_2777015370786200554079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025615 : Nat.totient 196256302761068522966886025615 = 152408276196159030784890531840 := by
  rw [← show ((([(5, 1), (43, 1), (167, 1), (5737, 1), (242161, 1), (3934410139910119, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_43, prime_oneHundredSixtySixFH_167, prime_oneHundredSixtySixFH_5737, prime_oneHundredSixtySixFH_242161, prime_oneHundredSixtySixFH_3934410139910119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025616 : Nat.totient 196256302761068522966886025616 = 82162503991403915122425567744 := by
  rw [← show ((([(2, 4), (7, 1), (53, 1), (229, 1), (144375745036626875144839, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_53, prime_oneHundredSixtySixFH_229, prime_oneHundredSixtySixFH_144375745036626875144839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025617 : Nat.totient 196256302761068522966886025617 = 112484997869039912104406795520 := by
  rw [← show ((([(3, 2), (11, 1), (19, 1), (569, 1), (11486099, 1), (15964304242953947, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_11, prime_oneHundredSixtySixFH_19, prime_oneHundredSixtySixFH_569, prime_oneHundredSixtySixFH_11486099, prime_oneHundredSixtySixFH_15964304242953947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025618 : Nat.totient 196256302761068522966886025618 = 98128151380474608877853740416 := by
  rw [← show ((([(2, 1), (1645038914297, 1), (59650960550358097, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_1645038914297, prime_oneHundredSixtySixFH_59650960550358097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025619 : Nat.totient 196256302761068522966886025619 = 189319947002499649467496181760 := by
  rw [← show ((([(31, 1), (349, 1), (3089, 1), (5872439941861824832609, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_31, prime_oneHundredSixtySixFH_349, prime_oneHundredSixtySixFH_3089, prime_oneHundredSixtySixFH_5872439941861824832609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025620 : Nat.totient 196256302761068522966886025620 = 52128886541770898609729329792 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (263, 1), (7307, 1), (1702070351494369974647, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_263, prime_oneHundredSixtySixFH_7307, prime_oneHundredSixtySixFH_1702070351494369974647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025621 : Nat.totient 196256302761068522966886025621 = 196256302761068522966886025620 := by
  rw [← show ((([(196256302761068522966886025621, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_196256302761068522966886025621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025622 : Nat.totient 196256302761068522966886025622 = 98100357515339225416171752168 := by
  rw [← show ((([(2, 1), (3539, 1), (1481527, 1), (18715588337908483487, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3539, prime_oneHundredSixtySixFH_1481527, prime_oneHundredSixtySixFH_18715588337908483487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025623 : Nat.totient 196256302761068522966886025623 = 112146456527577260464876588080 := by
  rw [← show ((([(3, 1), (7, 2), (51137599, 1), (26107539572420644691, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_51137599, prime_oneHundredSixtySixFH_26107539572420644691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025624 : Nat.totient 196256302761068522966886025624 = 98097531427839800486253802752 := by
  rw [← show ((([(2, 3), (3209, 1), (2397949, 1), (3188041503997964983, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3209, prime_oneHundredSixtySixFH_2397949, prime_oneHundredSixtySixFH_3188041503997964983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025625 : Nat.totient 196256302761068522966886025625 = 156852890925319616264341776000 := by
  rw [← show ((([(5, 4), (1033, 1), (968879, 1), (313742773378591663, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_1033, prime_oneHundredSixtySixFH_968879, prime_oneHundredSixtySixFH_313742773378591663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025626 : Nat.totient 196256302761068522966886025626 = 59646401592599850655991316480 := by
  rw [← show ((([(2, 1), (3, 2), (17, 1), (61, 1), (67, 1), (5449, 1), (41319599, 1), (696986943733, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_17, prime_oneHundredSixtySixFH_61, prime_oneHundredSixtySixFH_67, prime_oneHundredSixtySixFH_5449, prime_oneHundredSixtySixFH_41319599, prime_oneHundredSixtySixFH_696986943733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025627 : Nat.totient 196256302761068522966886025627 = 181159664087102685155383011840 := by
  rw [← show ((([(13, 1), (4839724377991, 1), (3119317856731969, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_13, prime_oneHundredSixtySixFH_4839724377991, prime_oneHundredSixtySixFH_3119317856731969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025628 : Nat.totient 196256302761068522966886025628 = 89207410345940237712220920720 := by
  rw [← show ((([(2, 2), (11, 1), (4460370517297011885611046037, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_11, prime_oneHundredSixtySixFH_4460370517297011885611046037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025629 : Nat.totient 196256302761068522966886025629 = 130793123289245224354073049600 := by
  rw [← show ((([(3, 1), (3041, 1), (94291, 1), (550349159, 1), (414550448467, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_3041, prime_oneHundredSixtySixFH_94291, prime_oneHundredSixtySixFH_550349159, prime_oneHundredSixtySixFH_414550448467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025630 : Nat.totient 196256302761068522966886025630 = 67287875232317341864323377184 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (1373897855507, 1), (2040662234661287, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_1373897855507, prime_oneHundredSixtySixFH_2040662234661287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025631 : Nat.totient 196256302761068522966886025631 = 187311133009023715844227595520 := by
  rw [← show ((([(23, 1), (463, 1), (31513, 1), (209821, 1), (2787251025765403, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_23, prime_oneHundredSixtySixFH_463, prime_oneHundredSixtySixFH_31513, prime_oneHundredSixtySixFH_209821, prime_oneHundredSixtySixFH_2787251025765403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025632 : Nat.totient 196256302761068522966886025632 = 65351694444637605444245702400 := by
  rw [← show ((([(2, 5), (3, 1), (983, 1), (124951, 1), (16644054374457931199, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_983, prime_oneHundredSixtySixFH_124951, prime_oneHundredSixtySixFH_16644054374457931199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025633 : Nat.totient 196256302761068522966886025633 = 196027832094291958912209789588 := by
  rw [← show ((([(859, 1), (228470666776564054676235187, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_859, prime_oneHundredSixtySixFH_228470666776564054676235187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025634 : Nat.totient 196256302761068522966886025634 = 96430099720534082076689368464 := by
  rw [← show ((([(2, 1), (59, 1), (2767, 1), (601080233628382090886189, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_59, prime_oneHundredSixtySixFH_2767, prime_oneHundredSixtySixFH_601080233628382090886189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025635 : Nat.totient 196256302761068522966886025635 = 104669638699795016412336559200 := by
  rw [← show ((([(3, 3), (5, 1), (268771, 1), (5408881132349583101431, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_268771, prime_oneHundredSixtySixFH_5408881132349583101431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025636 : Nat.totient 196256302761068522966886025636 = 92501654914805224896918979200 := by
  rw [← show ((([(2, 2), (19, 1), (271, 1), (787, 1), (81853, 1), (147921531993551131, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_19, prime_oneHundredSixtySixFH_271, prime_oneHundredSixtySixFH_787, prime_oneHundredSixtySixFH_81853, prime_oneHundredSixtySixFH_147921531993551131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025637 : Nat.totient 196256302761068522966886025637 = 168219688080915876828759450540 := by
  rw [← show ((([(7, 1), (28036614680152646138126575091, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_28036614680152646138126575091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025638 : Nat.totient 196256302761068522966886025638 = 65416761553243226047960779240 := by
  rw [← show ((([(2, 1), (3, 1), (32611, 1), (1003016889807470500582043, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_32611, prime_oneHundredSixtySixFH_1003016889807470500582043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025639 : Nat.totient 196256302761068522966886025639 = 178414525272290862798490671360 := by
  rw [← show ((([(11, 1), (603937, 1), (29541958961262594513077, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_11, prime_oneHundredSixtySixFH_603937, prime_oneHundredSixtySixFH_29541958961262594513077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025640 : Nat.totient 196256302761068522966886025640 = 72444594324292203729322782720 := by
  rw [← show ((([(2, 3), (5, 1), (13, 1), (3761, 1), (17540539, 1), (5721027051963583, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_13, prime_oneHundredSixtySixFH_3761, prime_oneHundredSixtySixFH_17540539, prime_oneHundredSixtySixFH_5721027051963583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025641 : Nat.totient 196256302761068522966886025641 = 129181363841760092726408822160 := by
  rw [← show ((([(3, 1), (79, 1), (133378175431, 1), (6208554457898603, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_79, prime_oneHundredSixtySixFH_133378175431, prime_oneHundredSixtySixFH_6208554457898603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025642 : Nat.totient 196256302761068522966886025642 = 98127463191744238871169248544 := by
  rw [← show ((([(2, 1), (142589, 1), (688188790022612273621689, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_142589, prime_oneHundredSixtySixFH_688188790022612273621689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025643 : Nat.totient 196256302761068522966886025643 = 171572685857015007049850179584 := by
  rw [← show ((([(17, 1), (29, 1), (37, 1), (89, 1), (120888492808254846913507, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_17, prime_oneHundredSixtySixFH_29, prime_oneHundredSixtySixFH_37, prime_oneHundredSixtySixFH_89, prime_oneHundredSixtySixFH_120888492808254846913507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025644 : Nat.totient 196256302761068522966886025644 = 56067873957886143728501768448 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (10639, 1), (660659, 1), (110801313211341497, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_10639, prime_oneHundredSixtySixFH_660659, prime_oneHundredSixtySixFH_110801313211341497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025645 : Nat.totient 196256302761068522966886025645 = 155564628977580920957238096960 := by
  rw [← show ((([(5, 1), (109, 1), (360103307818474354067680781, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_109, prime_oneHundredSixtySixFH_360103307818474354067680781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025646 : Nat.totient 196256302761068522966886025646 = 98128151380534261483443012822 := by
  rw [← show ((([(2, 1), (98128151380534261483443012823, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_98128151380534261483443012823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025647 : Nat.totient 196256302761068522966886025647 = 130837535174045681977924017096 := by
  rw [← show ((([(3, 1), (65418767587022840988962008549, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_65418767587022840988962008549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025648 : Nat.totient 196256302761068522966886025648 = 98128151369124237797479832000 := by
  rw [← show ((([(2, 4), (8600170751, 1), (1426252952145226853, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_8600170751, prime_oneHundredSixtySixFH_1426252952145226853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025649 : Nat.totient 196256302761068522966886025649 = 193486207229614160631799202880 := by
  rw [← show ((([(71, 1), (33427, 1), (1481947, 1), (65223539, 1), (855521309, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_71, prime_oneHundredSixtySixFH_33427, prime_oneHundredSixtySixFH_1481947, prime_oneHundredSixtySixFH_65223539, prime_oneHundredSixtySixFH_855521309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025650 : Nat.totient 196256302761068522966886025650 = 44919545535718692874464000000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (11, 1), (31, 1), (41, 1), (232554011, 1), (402411407710181, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_11, prime_oneHundredSixtySixFH_31, prime_oneHundredSixtySixFH_41, prime_oneHundredSixtySixFH_232554011, prime_oneHundredSixtySixFH_402411407710181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025651 : Nat.totient 196256302761068522966886025651 = 167933112323081917135796616384 := by
  rw [← show ((([(7, 1), (587, 1), (349851193, 1), (136522462290122423, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_587, prime_oneHundredSixtySixFH_349851193, prime_oneHundredSixtySixFH_136522462290122423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025652 : Nat.totient 196256302761068522966886025652 = 97695860036670815419879895040 := by
  rw [← show ((([(2, 2), (227, 1), (13902431, 1), (57096913, 1), (272291690273, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_227, prime_oneHundredSixtySixFH_13902431, prime_oneHundredSixtySixFH_57096913, prime_oneHundredSixtySixFH_272291690273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025653 : Nat.totient 196256302761068522966886025653 = 119460779900472625673015468160 := by
  rw [← show ((([(3, 2), (13, 1), (131, 1), (307, 1), (45181883, 1), (923131888658219, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_13, prime_oneHundredSixtySixFH_131, prime_oneHundredSixtySixFH_307, prime_oneHundredSixtySixFH_45181883, prime_oneHundredSixtySixFH_923131888658219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025654 : Nat.totient 196256302761068522966886025654 = 93778699544882331666278539200 := by
  rw [← show ((([(2, 1), (23, 1), (1151, 1), (64123, 1), (57806493343951883513, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_23, prime_oneHundredSixtySixFH_1151, prime_oneHundredSixtySixFH_64123, prime_oneHundredSixtySixFH_57806493343951883513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025655 : Nat.totient 196256302761068522966886025655 = 148142410526088618590172788352 := by
  rw [← show ((([(5, 1), (19, 1), (269, 1), (3203, 1), (2397677616984963445807, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_19, prime_oneHundredSixtySixFH_269, prime_oneHundredSixtySixFH_3203, prime_oneHundredSixtySixFH_2397677616984963445807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025656 : Nat.totient 196256302761068522966886025656 = 65418302146521221067431064960 := by
  rw [← show ((([(2, 3), (3, 1), (140557, 1), (4272126527, 1), (13618077000271, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_140557, prime_oneHundredSixtySixFH_4272126527, prime_oneHundredSixtySixFH_13618077000271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025657 : Nat.totient 196256302761068522966886025657 = 196256302761068522966886025656 := by
  rw [← show ((([(196256302761068522966886025657, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_196256302761068522966886025657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025658 : Nat.totient 196256302761068522966886025658 = 82153801155796125893115080256 := by
  rw [← show ((([(2, 1), (7, 1), (43, 1), (326007147443635420210774129, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_43, prime_oneHundredSixtySixFH_326007147443635420210774129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025659 : Nat.totient 196256302761068522966886025659 = 129045240171644161788915944256 := by
  rw [← show ((([(3, 1), (73, 1), (7973332828259, 1), (112393088372779, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_73, prime_oneHundredSixtySixFH_7973332828259, prime_oneHundredSixtySixFH_112393088372779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025660 : Nat.totient 196256302761068522966886025660 = 72008450480059725643363123200 := by
  rw [← show ((([(2, 2), (5, 1), (17, 1), (47, 1), (241, 1), (17117, 1), (2977159790395854961, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_17, prime_oneHundredSixtySixFH_47, prime_oneHundredSixtySixFH_241, prime_oneHundredSixtySixFH_17117, prime_oneHundredSixtySixFH_2977159790395854961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025661 : Nat.totient 196256302761068522966886025661 = 178414820691863268411637988320 := by
  rw [← show ((([(11, 1), (10431972312767, 1), (1710269308072553, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_11, prime_oneHundredSixtySixFH_10431972312767, prime_oneHundredSixtySixFH_1710269308072553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025662 : Nat.totient 196256302761068522966886025662 = 65243382127580067337779171840 := by
  rw [← show ((([(2, 1), (3, 4), (373, 1), (2770116577, 1), (1172469949234931, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_373, prime_oneHundredSixtySixFH_2770116577, prime_oneHundredSixtySixFH_1172469949234931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025663 : Nat.totient 196256302761068522966886025663 = 196256295229495060245242698848 := by
  rw [← show ((([(26057809, 1), (7531573462721617269007, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_26057809, prime_oneHundredSixtySixFH_7531573462721617269007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025664 : Nat.totient 196256302761068522966886025664 = 98128064575403285188398022656 := by
  rw [← show ((([(2, 6), (1130497, 1), (31803155147, 1), (85291159189, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_1130497, prime_oneHundredSixtySixFH_31803155147, prime_oneHundredSixtySixFH_85291159189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025665 : Nat.totient 196256302761068522966886025665 = 89717166976488467642005040256 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (1869107645343509742541771673, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_1869107645343509742541771673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025666 : Nat.totient 196256302761068522966886025666 = 90578241277126864360824816000 := by
  rw [← show ((([(2, 1), (13, 1), (56941, 1), (132563870268596862722201, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_13, prime_oneHundredSixtySixFH_56941, prime_oneHundredSixtySixFH_132563870268596862722201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025667 : Nat.totient 196256302761068522966886025667 = 196256277707768905285348588800 := by
  rw [← show ((([(7835909, 1), (26778232801, 1), (935302976263, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_7835909, prime_oneHundredSixtySixFH_26778232801, prime_oneHundredSixtySixFH_935302976263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025668 : Nat.totient 196256302761068522966886025668 = 65373111668576280948472504320 := by
  rw [← show ((([(2, 2), (3, 1), (1433, 1), (21468827, 1), (52311409, 1), (10162286681, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_1433, prime_oneHundredSixtySixFH_21468827, prime_oneHundredSixtySixFH_52311409, prime_oneHundredSixtySixFH_10162286681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025669 : Nat.totient 196256302761068522966886025669 = 192547624989543659556904984320 := by
  rw [← show ((([(53, 1), (34667, 1), (1104739, 1), (96687826363073521, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_53, prime_oneHundredSixtySixFH_34667, prime_oneHundredSixtySixFH_1104739, prime_oneHundredSixtySixFH_96687826363073521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025670 : Nat.totient 196256302761068522966886025670 = 78342638169387842161934134560 := by
  rw [← show ((([(2, 1), (5, 1), (491, 1), (39970733759891756205068437, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_491, prime_oneHundredSixtySixFH_39970733759891756205068437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025671 : Nat.totient 196256302761068522966886025671 = 130837535174029175483211478320 := by
  rw [← show ((([(3, 2), (7949397798341, 1), (2743133054291459, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_7949397798341, prime_oneHundredSixtySixFH_2743133054291459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025672 : Nat.totient 196256302761068522966886025672 = 73826822354755448187245514240 := by
  rw [← show ((([(2, 3), (7, 2), (11, 1), (29, 1), (148106475317, 1), (10596753118267, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_11, prime_oneHundredSixtySixFH_29, prime_oneHundredSixtySixFH_148106475317, prime_oneHundredSixtySixFH_10596753118267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025673 : Nat.totient 196256302761068522966886025673 = 192381591189057704463586314240 := by
  rw [← show ((([(103, 1), (113, 1), (773, 1), (1002569, 1), (21757759853982811, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_103, prime_oneHundredSixtySixFH_113, prime_oneHundredSixtySixFH_773, prime_oneHundredSixtySixFH_1002569, prime_oneHundredSixtySixFH_21757759853982811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025674 : Nat.totient 196256302761068522966886025674 = 61361997983651092385577902400 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (101, 1), (1095119, 1), (15564532260361971239, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_19, prime_oneHundredSixtySixFH_101, prime_oneHundredSixtySixFH_1095119, prime_oneHundredSixtySixFH_15564532260361971239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025675 : Nat.totient 196256302761068522966886025675 = 155733022398774679390877875200 := by
  rw [← show ((([(5, 2), (137, 1), (1237, 1), (11808541243, 1), (3922808311181, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_137, prime_oneHundredSixtySixFH_1237, prime_oneHundredSixtySixFH_11808541243, prime_oneHundredSixtySixFH_3922808311181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025676 : Nat.totient 196256302761068522966886025676 = 97451948583173561965457760000 := by
  rw [← show ((([(2, 2), (151, 1), (3701, 1), (17064653, 1), (35586779, 1), (144571087, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_151, prime_oneHundredSixtySixFH_3701, prime_oneHundredSixtySixFH_17064653, prime_oneHundredSixtySixFH_35586779, prime_oneHundredSixtySixFH_144571087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025677 : Nat.totient 196256302761068522966886025677 = 117787243940609516562407219200 := by
  rw [← show ((([(3, 1), (17, 2), (23, 1), (94896739697, 1), (103711135101401, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_17, prime_oneHundredSixtySixFH_23, prime_oneHundredSixtySixFH_94896739697, prime_oneHundredSixtySixFH_103711135101401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025678 : Nat.totient 196256302761068522966886025678 = 97969735385460672148414470240 := by
  rw [← show ((([(2, 1), (1103, 1), (1549, 1), (15907, 1), (3610591921017462991, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_1103, prime_oneHundredSixtySixFH_1549, prime_oneHundredSixtySixFH_15907, prime_oneHundredSixtySixFH_3610591921017462991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025679 : Nat.totient 196256302761068522966886025679 = 154162591758353570334271627392 := by
  rw [← show ((([(7, 1), (13, 1), (139, 1), (1801284427, 1), (8613608449555973, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_13, prime_oneHundredSixtySixFH_139, prime_oneHundredSixtySixFH_1801284427, prime_oneHundredSixtySixFH_8613608449555973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025680 : Nat.totient 196256302761068522966886025680 = 50578805541829151083435683840 := by
  rw [← show ((([(2, 4), (3, 2), (5, 1), (37, 1), (149, 1), (26121592171, 1), (1892794561403, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_37, prime_oneHundredSixtySixFH_149, prime_oneHundredSixtySixFH_26121592171, prime_oneHundredSixtySixFH_1892794561403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025681 : Nat.totient 196256302761068522966886025681 = 189922596329773047862720739520 := by
  rw [← show ((([(31, 1), (118543, 1), (191827, 1), (714773, 1), (389500600367, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_31, prime_oneHundredSixtySixFH_118543, prime_oneHundredSixtySixFH_191827, prime_oneHundredSixtySixFH_714773, prime_oneHundredSixtySixFH_389500600367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025682 : Nat.totient 196256302761068522966886025682 = 98105122009170606411515422800 := by
  rw [← show ((([(2, 1), (4261, 1), (23029371363655071927585781, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_4261, prime_oneHundredSixtySixFH_23029371363655071927585781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025683 : Nat.totient 196256302761068522966886025683 = 117253585139285881400528256000 := by
  rw [← show ((([(3, 1), (11, 1), (83, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_11, prime_oneHundredSixtySixFH_83, prime_oneHundredSixtySixFH_461, prime_oneHundredSixtySixFH_69997, prime_oneHundredSixtySixFH_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025684 : Nat.totient 196256302761068522966886025684 = 97697906312123292386522856480 := by
  rw [← show ((([(2, 2), (283, 1), (1171, 1), (148054049694070577054197, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_283, prime_oneHundredSixtySixFH_1171, prime_oneHundredSixtySixFH_148054049694070577054197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025685 : Nat.totient 196256302761068522966886025685 = 156892388268813194924307360000 := by
  rw [← show ((([(5, 1), (1451, 1), (35869, 1), (2090173, 1), (360815091211451, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_1451, prime_oneHundredSixtySixFH_35869, prime_oneHundredSixtySixFH_2090173, prime_oneHundredSixtySixFH_360815091211451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025686 : Nat.totient 196256302761068522966886025686 = 56073229351460452504720863936 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (6339654679, 1), (737069974621369177, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_6339654679, prime_oneHundredSixtySixFH_737069974621369177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025687 : Nat.totient 196256302761068522966886025687 = 191045203165851494852752588800 := by
  rw [← show ((([(61, 1), (97, 1), (51769, 1), (1866992089, 1), (343170375571, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_61, prime_oneHundredSixtySixFH_97, prime_oneHundredSixtySixFH_51769, prime_oneHundredSixtySixFH_1866992089, prime_oneHundredSixtySixFH_343170375571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025688 : Nat.totient 196256302761068522966886025688 = 97522870946926682221170286080 := by
  rw [← show ((([(2, 3), (197, 1), (911, 1), (136693864861693600332433, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_197, prime_oneHundredSixtySixFH_911, prime_oneHundredSixtySixFH_136693864861693600332433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025689 : Nat.totient 196256302761068522966886025689 = 130837535173841601305281545360 := by
  rw [← show ((([(3, 3), (641143194221, 1), (11337174003609767, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_641143194221, prime_oneHundredSixtySixFH_11337174003609767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025690 : Nat.totient 196256302761068522966886025690 = 78502429002458602235389697280 := by
  rw [← show ((([(2, 1), (5, 1), (904721, 1), (14722607, 1), (1473412067746327, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_904721, prime_oneHundredSixtySixFH_14722607, prime_oneHundredSixtySixFH_1473412067746327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025691 : Nat.totient 196256302761068522966886025691 = 191469563669335144357937586000 := by
  rw [← show ((([(41, 1), (4786739091733378608948439651, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_41, prime_oneHundredSixtySixFH_4786739091733378608948439651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025692 : Nat.totient 196256302761068522966886025692 = 60372415956613482201509319360 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (4271, 1), (294557064581447512692767, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_13, prime_oneHundredSixtySixFH_4271, prime_oneHundredSixtySixFH_294557064581447512692767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025693 : Nat.totient 196256302761068522966886025693 = 154326619190320843290356559744 := by
  rw [← show ((([(7, 1), (19, 1), (59, 1), (67, 1), (373288970137971775442057, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_19, prime_oneHundredSixtySixFH_59, prime_oneHundredSixtySixFH_67, prime_oneHundredSixtySixFH_373288970137971775442057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025694 : Nat.totient 196256302761068522966886025694 = 83959838040167062397327451520 := by
  rw [← show ((([(2, 1), (11, 1), (17, 1), (1082243, 1), (484872133728911038367, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_11, prime_oneHundredSixtySixFH_17, prime_oneHundredSixtySixFH_1082243, prime_oneHundredSixtySixFH_484872133728911038367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025695 : Nat.totient 196256302761068522966886025695 = 104670028139069208690815500160 := by
  rw [← show ((([(3, 1), (5, 1), (625523501861, 1), (20916485916962333, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_625523501861, prime_oneHundredSixtySixFH_20916485916962333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025696 : Nat.totient 196256302761068522966886025696 = 97489903174029323674762199040 := by
  rw [← show ((([(2, 5), (181, 1), (1019, 1), (289049, 1), (115040140797397073, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_181, prime_oneHundredSixtySixFH_1019, prime_oneHundredSixtySixFH_289049, prime_oneHundredSixtySixFH_115040140797397073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025697 : Nat.totient 196256302761068522966886025697 = 196245025819206584813201714112 := by
  rw [← show ((([(22717, 1), (74623, 1), (24826469, 1), (4663210013743, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_22717, prime_oneHundredSixtySixFH_74623, prime_oneHundredSixtySixFH_24826469, prime_oneHundredSixtySixFH_4663210013743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025698 : Nat.totient 196256302761068522966886025698 = 65418622218121556770201902744 := by
  rw [← show ((([(2, 1), (3, 2), (450019, 1), (24228150214036459567619, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_450019, prime_oneHundredSixtySixFH_24228150214036459567619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025699 : Nat.totient 196256302761068522966886025699 = 195836018458111540035612933120 := by
  rw [← show ((([(673, 1), (1523, 1), (191473486540766711285681, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_673, prime_oneHundredSixtySixFH_1523, prime_oneHundredSixtySixFH_191473486540766711285681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025700 : Nat.totient 196256302761068522966886025700 = 64001258811647136405341752320 := by
  rw [← show ((([(2, 2), (5, 2), (7, 1), (23, 1), (179, 1), (42937, 1), (1586035883628851219, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_2, prime_oneHundredSixtySixFH_5, prime_oneHundredSixtySixFH_7, prime_oneHundredSixtySixFH_23, prime_oneHundredSixtySixFH_179, prime_oneHundredSixtySixFH_42937, prime_oneHundredSixtySixFH_1586035883628851219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtySixFH_196256302761068522966886025701 : Nat.totient 196256302761068522966886025701 = 123388084494529047318395061120 := by
  rw [← show ((([(3, 1), (29, 1), (43, 1), (52460920278286159574147561, 1)] : List FactorBlock).map factorBlockValue).prod) = 196256302761068522966886025701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtySixFH_3, prime_oneHundredSixtySixFH_29, prime_oneHundredSixtySixFH_43, prime_oneHundredSixtySixFH_52460920278286159574147561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixtySixFH : certifiedKill 1 196256302761068522966886025599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixtySixFH_196256302761068522966886025600, phi_oneHundredSixtySixFH_196256302761068522966886025601, phi_oneHundredSixtySixFH_196256302761068522966886025602,
    phi_oneHundredSixtySixFH_196256302761068522966886025603, phi_oneHundredSixtySixFH_196256302761068522966886025604, phi_oneHundredSixtySixFH_196256302761068522966886025605,
    phi_oneHundredSixtySixFH_196256302761068522966886025606, phi_oneHundredSixtySixFH_196256302761068522966886025607, phi_oneHundredSixtySixFH_196256302761068522966886025608,
    phi_oneHundredSixtySixFH_196256302761068522966886025609, phi_oneHundredSixtySixFH_196256302761068522966886025610, phi_oneHundredSixtySixFH_196256302761068522966886025611,
    phi_oneHundredSixtySixFH_196256302761068522966886025612, phi_oneHundredSixtySixFH_196256302761068522966886025613, phi_oneHundredSixtySixFH_196256302761068522966886025614,
    phi_oneHundredSixtySixFH_196256302761068522966886025615, phi_oneHundredSixtySixFH_196256302761068522966886025616, phi_oneHundredSixtySixFH_196256302761068522966886025617,
    phi_oneHundredSixtySixFH_196256302761068522966886025618, phi_oneHundredSixtySixFH_196256302761068522966886025619, phi_oneHundredSixtySixFH_196256302761068522966886025620,
    phi_oneHundredSixtySixFH_196256302761068522966886025621, phi_oneHundredSixtySixFH_196256302761068522966886025622, phi_oneHundredSixtySixFH_196256302761068522966886025623,
    phi_oneHundredSixtySixFH_196256302761068522966886025624, phi_oneHundredSixtySixFH_196256302761068522966886025625, phi_oneHundredSixtySixFH_196256302761068522966886025626,
    phi_oneHundredSixtySixFH_196256302761068522966886025627, phi_oneHundredSixtySixFH_196256302761068522966886025628, phi_oneHundredSixtySixFH_196256302761068522966886025629,
    phi_oneHundredSixtySixFH_196256302761068522966886025630, phi_oneHundredSixtySixFH_196256302761068522966886025631, phi_oneHundredSixtySixFH_196256302761068522966886025632,
    phi_oneHundredSixtySixFH_196256302761068522966886025633, phi_oneHundredSixtySixFH_196256302761068522966886025634, phi_oneHundredSixtySixFH_196256302761068522966886025635,
    phi_oneHundredSixtySixFH_196256302761068522966886025636, phi_oneHundredSixtySixFH_196256302761068522966886025637, phi_oneHundredSixtySixFH_196256302761068522966886025638,
    phi_oneHundredSixtySixFH_196256302761068522966886025639, phi_oneHundredSixtySixFH_196256302761068522966886025640, phi_oneHundredSixtySixFH_196256302761068522966886025641,
    phi_oneHundredSixtySixFH_196256302761068522966886025642, phi_oneHundredSixtySixFH_196256302761068522966886025643, phi_oneHundredSixtySixFH_196256302761068522966886025644,
    phi_oneHundredSixtySixFH_196256302761068522966886025645, phi_oneHundredSixtySixFH_196256302761068522966886025646, phi_oneHundredSixtySixFH_196256302761068522966886025647,
    phi_oneHundredSixtySixFH_196256302761068522966886025648, phi_oneHundredSixtySixFH_196256302761068522966886025649, phi_oneHundredSixtySixFH_196256302761068522966886025650,
    phi_oneHundredSixtySixFH_196256302761068522966886025651, phi_oneHundredSixtySixFH_196256302761068522966886025652, phi_oneHundredSixtySixFH_196256302761068522966886025653,
    phi_oneHundredSixtySixFH_196256302761068522966886025654, phi_oneHundredSixtySixFH_196256302761068522966886025655, phi_oneHundredSixtySixFH_196256302761068522966886025656,
    phi_oneHundredSixtySixFH_196256302761068522966886025657, phi_oneHundredSixtySixFH_196256302761068522966886025658, phi_oneHundredSixtySixFH_196256302761068522966886025659,
    phi_oneHundredSixtySixFH_196256302761068522966886025660, phi_oneHundredSixtySixFH_196256302761068522966886025661, phi_oneHundredSixtySixFH_196256302761068522966886025662,
    phi_oneHundredSixtySixFH_196256302761068522966886025663, phi_oneHundredSixtySixFH_196256302761068522966886025664, phi_oneHundredSixtySixFH_196256302761068522966886025665,
    phi_oneHundredSixtySixFH_196256302761068522966886025666, phi_oneHundredSixtySixFH_196256302761068522966886025667, phi_oneHundredSixtySixFH_196256302761068522966886025668,
    phi_oneHundredSixtySixFH_196256302761068522966886025669, phi_oneHundredSixtySixFH_196256302761068522966886025670, phi_oneHundredSixtySixFH_196256302761068522966886025671,
    phi_oneHundredSixtySixFH_196256302761068522966886025672, phi_oneHundredSixtySixFH_196256302761068522966886025673, phi_oneHundredSixtySixFH_196256302761068522966886025674,
    phi_oneHundredSixtySixFH_196256302761068522966886025675, phi_oneHundredSixtySixFH_196256302761068522966886025676, phi_oneHundredSixtySixFH_196256302761068522966886025677,
    phi_oneHundredSixtySixFH_196256302761068522966886025678, phi_oneHundredSixtySixFH_196256302761068522966886025679, phi_oneHundredSixtySixFH_196256302761068522966886025680,
    phi_oneHundredSixtySixFH_196256302761068522966886025681, phi_oneHundredSixtySixFH_196256302761068522966886025682, phi_oneHundredSixtySixFH_196256302761068522966886025683,
    phi_oneHundredSixtySixFH_196256302761068522966886025684, phi_oneHundredSixtySixFH_196256302761068522966886025685, phi_oneHundredSixtySixFH_196256302761068522966886025686,
    phi_oneHundredSixtySixFH_196256302761068522966886025687, phi_oneHundredSixtySixFH_196256302761068522966886025688, phi_oneHundredSixtySixFH_196256302761068522966886025689,
    phi_oneHundredSixtySixFH_196256302761068522966886025690, phi_oneHundredSixtySixFH_196256302761068522966886025691, phi_oneHundredSixtySixFH_196256302761068522966886025692,
    phi_oneHundredSixtySixFH_196256302761068522966886025693, phi_oneHundredSixtySixFH_196256302761068522966886025694, phi_oneHundredSixtySixFH_196256302761068522966886025695,
    phi_oneHundredSixtySixFH_196256302761068522966886025696, phi_oneHundredSixtySixFH_196256302761068522966886025697, phi_oneHundredSixtySixFH_196256302761068522966886025698,
    phi_oneHundredSixtySixFH_196256302761068522966886025699, phi_oneHundredSixtySixFH_196256302761068522966886025700, phi_oneHundredSixtySixFH_196256302761068522966886025701
    ]

end TotientTailPeriodKiller
end Erdos249257

