import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def ninetyNineCSFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem ninetyNineCSFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : ninetyNineCSFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [ninetyNineCSFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [ninetyNineCSFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then ninetyNineCSFastPow a n * ninetyNineCSFastPow a n * a else ninetyNineCSFastPow a n * ninetyNineCSFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_ninetyNineCS_2 : Nat.Prime 2 := by norm_num

private theorem prime_ninetyNineCS_3 : Nat.Prime 3 := by norm_num

private theorem prime_ninetyNineCS_5 : Nat.Prime 5 := by norm_num

private theorem prime_ninetyNineCS_7 : Nat.Prime 7 := by norm_num

private theorem prime_ninetyNineCS_11 : Nat.Prime 11 := by norm_num

private theorem prime_ninetyNineCS_13 : Nat.Prime 13 := by norm_num

private theorem prime_ninetyNineCS_17 : Nat.Prime 17 := by norm_num

private theorem prime_ninetyNineCS_19 : Nat.Prime 19 := by norm_num

private theorem prime_ninetyNineCS_23 : Nat.Prime 23 := by norm_num

private theorem prime_ninetyNineCS_29 : Nat.Prime 29 := by norm_num

private theorem prime_ninetyNineCS_31 : Nat.Prime 31 := by norm_num

private theorem prime_ninetyNineCS_37 : Nat.Prime 37 := by norm_num

private theorem prime_ninetyNineCS_41 : Nat.Prime 41 := by norm_num

private theorem prime_ninetyNineCS_43 : Nat.Prime 43 := by norm_num

private theorem prime_ninetyNineCS_47 : Nat.Prime 47 := by norm_num

private theorem prime_ninetyNineCS_53 : Nat.Prime 53 := by norm_num

private theorem prime_ninetyNineCS_59 : Nat.Prime 59 := by norm_num

private theorem prime_ninetyNineCS_61 : Nat.Prime 61 := by norm_num

private theorem prime_ninetyNineCS_67 : Nat.Prime 67 := by norm_num

private theorem prime_ninetyNineCS_71 : Nat.Prime 71 := by norm_num

private theorem prime_ninetyNineCS_73 : Nat.Prime 73 := by norm_num

private theorem prime_ninetyNineCS_79 : Nat.Prime 79 := by norm_num

private theorem prime_ninetyNineCS_83 : Nat.Prime 83 := by norm_num

private theorem prime_ninetyNineCS_89 : Nat.Prime 89 := by norm_num

private theorem prime_ninetyNineCS_97 : Nat.Prime 97 := by norm_num

private theorem prime_ninetyNineCS_101 : Nat.Prime 101 := by norm_num

private theorem prime_ninetyNineCS_103 : Nat.Prime 103 := by norm_num

private theorem prime_ninetyNineCS_107 : Nat.Prime 107 := by norm_num

private theorem prime_ninetyNineCS_109 : Nat.Prime 109 := by norm_num

private theorem prime_ninetyNineCS_113 : Nat.Prime 113 := by norm_num

private theorem prime_ninetyNineCS_127 : Nat.Prime 127 := by norm_num

private theorem prime_ninetyNineCS_131 : Nat.Prime 131 := by norm_num

private theorem prime_ninetyNineCS_137 : Nat.Prime 137 := by norm_num

private theorem prime_ninetyNineCS_139 : Nat.Prime 139 := by norm_num

private theorem prime_ninetyNineCS_149 : Nat.Prime 149 := by norm_num

private theorem prime_ninetyNineCS_151 : Nat.Prime 151 := by norm_num

private theorem prime_ninetyNineCS_157 : Nat.Prime 157 := by norm_num

private theorem prime_ninetyNineCS_163 : Nat.Prime 163 := by norm_num

private theorem prime_ninetyNineCS_167 : Nat.Prime 167 := by norm_num

private theorem prime_ninetyNineCS_173 : Nat.Prime 173 := by norm_num

private theorem prime_ninetyNineCS_179 : Nat.Prime 179 := by norm_num

private theorem prime_ninetyNineCS_181 : Nat.Prime 181 := by norm_num

private theorem prime_ninetyNineCS_191 : Nat.Prime 191 := by norm_num

private theorem prime_ninetyNineCS_193 : Nat.Prime 193 := by norm_num

private theorem prime_ninetyNineCS_197 : Nat.Prime 197 := by norm_num

private theorem prime_ninetyNineCS_211 : Nat.Prime 211 := by norm_num

private theorem prime_ninetyNineCS_223 : Nat.Prime 223 := by norm_num

private theorem prime_ninetyNineCS_227 : Nat.Prime 227 := by norm_num

private theorem prime_ninetyNineCS_233 : Nat.Prime 233 := by norm_num

private theorem prime_ninetyNineCS_239 : Nat.Prime 239 := by norm_num

private theorem prime_ninetyNineCS_241 : Nat.Prime 241 := by norm_num

private theorem prime_ninetyNineCS_251 : Nat.Prime 251 := by norm_num

private theorem prime_ninetyNineCS_257 : Nat.Prime 257 := by norm_num

private theorem prime_ninetyNineCS_269 : Nat.Prime 269 := by norm_num

private theorem prime_ninetyNineCS_271 : Nat.Prime 271 := by norm_num

private theorem prime_ninetyNineCS_277 : Nat.Prime 277 := by norm_num

private theorem prime_ninetyNineCS_283 : Nat.Prime 283 := by norm_num

private theorem prime_ninetyNineCS_311 : Nat.Prime 311 := by norm_num

private theorem prime_ninetyNineCS_313 : Nat.Prime 313 := by norm_num

private theorem prime_ninetyNineCS_317 : Nat.Prime 317 := by norm_num

private theorem prime_ninetyNineCS_331 : Nat.Prime 331 := by norm_num

private theorem prime_ninetyNineCS_337 : Nat.Prime 337 := by norm_num

private theorem prime_ninetyNineCS_347 : Nat.Prime 347 := by norm_num

private theorem prime_ninetyNineCS_349 : Nat.Prime 349 := by norm_num

private theorem prime_ninetyNineCS_359 : Nat.Prime 359 := by norm_num

private theorem prime_ninetyNineCS_379 : Nat.Prime 379 := by norm_num

private theorem prime_ninetyNineCS_383 : Nat.Prime 383 := by norm_num

private theorem prime_ninetyNineCS_389 : Nat.Prime 389 := by norm_num

private theorem prime_ninetyNineCS_401 : Nat.Prime 401 := by norm_num

private theorem prime_ninetyNineCS_439 : Nat.Prime 439 := by norm_num

private theorem prime_ninetyNineCS_457 : Nat.Prime 457 := by norm_num

private theorem prime_ninetyNineCS_463 : Nat.Prime 463 := by norm_num

private theorem prime_ninetyNineCS_467 : Nat.Prime 467 := by norm_num

private theorem prime_ninetyNineCS_479 : Nat.Prime 479 := by norm_num

private theorem prime_ninetyNineCS_487 : Nat.Prime 487 := by norm_num

private theorem prime_ninetyNineCS_499 : Nat.Prime 499 := by norm_num

private theorem prime_ninetyNineCS_503 : Nat.Prime 503 := by norm_num

private theorem prime_ninetyNineCS_523 : Nat.Prime 523 := by norm_num

private theorem prime_ninetyNineCS_541 : Nat.Prime 541 := by norm_num

private theorem prime_ninetyNineCS_547 : Nat.Prime 547 := by norm_num

private theorem prime_ninetyNineCS_557 : Nat.Prime 557 := by norm_num

private theorem prime_ninetyNineCS_563 : Nat.Prime 563 := by norm_num

private theorem prime_ninetyNineCS_569 : Nat.Prime 569 := by norm_num

private theorem prime_ninetyNineCS_577 : Nat.Prime 577 := by norm_num

private theorem prime_ninetyNineCS_601 : Nat.Prime 601 := by norm_num

private theorem prime_ninetyNineCS_617 : Nat.Prime 617 := by norm_num

private theorem prime_ninetyNineCS_647 : Nat.Prime 647 := by norm_num

private theorem prime_ninetyNineCS_659 : Nat.Prime 659 := by norm_num

private theorem prime_ninetyNineCS_691 : Nat.Prime 691 := by norm_num

private theorem prime_ninetyNineCS_719 : Nat.Prime 719 := by norm_num

private theorem prime_ninetyNineCS_739 : Nat.Prime 739 := by norm_num

private theorem prime_ninetyNineCS_743 : Nat.Prime 743 := by norm_num

private theorem prime_ninetyNineCS_811 : Nat.Prime 811 := by norm_num

private theorem prime_ninetyNineCS_823 : Nat.Prime 823 := by norm_num

private theorem prime_ninetyNineCS_829 : Nat.Prime 829 := by norm_num

private theorem prime_ninetyNineCS_857 : Nat.Prime 857 := by norm_num

private theorem prime_ninetyNineCS_859 : Nat.Prime 859 := by norm_num

private theorem prime_ninetyNineCS_887 : Nat.Prime 887 := by norm_num

private theorem prime_ninetyNineCS_911 : Nat.Prime 911 := by norm_num

private theorem prime_ninetyNineCS_937 : Nat.Prime 937 := by norm_num

private theorem prime_ninetyNineCS_947 : Nat.Prime 947 := by norm_num

private theorem prime_ninetyNineCS_977 : Nat.Prime 977 := by norm_num

private theorem prime_ninetyNineCS_983 : Nat.Prime 983 := by norm_num

private theorem prime_ninetyNineCS_991 : Nat.Prime 991 := by norm_num

private theorem prime_ninetyNineCS_997 : Nat.Prime 997 := by norm_num

private theorem prime_ninetyNineCS_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_ninetyNineCS_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_ninetyNineCS_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_ninetyNineCS_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_ninetyNineCS_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_ninetyNineCS_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_ninetyNineCS_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_ninetyNineCS_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_ninetyNineCS_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_ninetyNineCS_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_ninetyNineCS_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_ninetyNineCS_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_ninetyNineCS_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_ninetyNineCS_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_ninetyNineCS_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_ninetyNineCS_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_ninetyNineCS_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_ninetyNineCS_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_ninetyNineCS_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_ninetyNineCS_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_ninetyNineCS_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_ninetyNineCS_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_ninetyNineCS_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_ninetyNineCS_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_ninetyNineCS_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_ninetyNineCS_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_ninetyNineCS_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_ninetyNineCS_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_ninetyNineCS_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_ninetyNineCS_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_ninetyNineCS_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_ninetyNineCS_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_ninetyNineCS_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_ninetyNineCS_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_ninetyNineCS_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_ninetyNineCS_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_ninetyNineCS_2017 : Nat.Prime 2017 := by norm_num

private theorem prime_ninetyNineCS_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_ninetyNineCS_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_ninetyNineCS_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_ninetyNineCS_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_ninetyNineCS_2161 : Nat.Prime 2161 := by norm_num

private theorem prime_ninetyNineCS_2293 : Nat.Prime 2293 := by norm_num

private theorem prime_ninetyNineCS_2371 : Nat.Prime 2371 := by norm_num

private theorem prime_ninetyNineCS_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_ninetyNineCS_2417 : Nat.Prime 2417 := by norm_num

private theorem prime_ninetyNineCS_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_ninetyNineCS_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_ninetyNineCS_2671 : Nat.Prime 2671 := by norm_num

private theorem prime_ninetyNineCS_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_ninetyNineCS_2713 : Nat.Prime 2713 := by norm_num

private theorem prime_ninetyNineCS_2851 : Nat.Prime 2851 := by norm_num

private theorem prime_ninetyNineCS_3019 : Nat.Prime 3019 := by norm_num

private theorem prime_ninetyNineCS_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_ninetyNineCS_3359 : Nat.Prime 3359 := by norm_num

private theorem prime_ninetyNineCS_3361 : Nat.Prime 3361 := by norm_num

private theorem prime_ninetyNineCS_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_ninetyNineCS_3499 : Nat.Prime 3499 := by norm_num

private theorem prime_ninetyNineCS_3541 : Nat.Prime 3541 := by norm_num

private theorem prime_ninetyNineCS_3583 : Nat.Prime 3583 := by norm_num

private theorem prime_ninetyNineCS_3613 : Nat.Prime 3613 := by norm_num

private theorem prime_ninetyNineCS_3643 : Nat.Prime 3643 := by norm_num

private theorem prime_ninetyNineCS_3803 : Nat.Prime 3803 := by norm_num

private theorem prime_ninetyNineCS_3917 : Nat.Prime 3917 := by norm_num

private theorem prime_ninetyNineCS_3929 : Nat.Prime 3929 := by norm_num

private theorem prime_ninetyNineCS_3947 : Nat.Prime 3947 := by norm_num

private theorem prime_ninetyNineCS_4007 : Nat.Prime 4007 := by norm_num

private theorem prime_ninetyNineCS_4153 : Nat.Prime 4153 := by norm_num

private theorem prime_ninetyNineCS_4391 : Nat.Prime 4391 := by norm_num

private theorem prime_ninetyNineCS_4397 : Nat.Prime 4397 := by norm_num

private theorem prime_ninetyNineCS_4507 : Nat.Prime 4507 := by norm_num

private theorem prime_ninetyNineCS_4549 : Nat.Prime 4549 := by norm_num

private theorem prime_ninetyNineCS_4751 : Nat.Prime 4751 := by norm_num

private theorem prime_ninetyNineCS_4813 : Nat.Prime 4813 := by norm_num

private theorem prime_ninetyNineCS_4909 : Nat.Prime 4909 := by norm_num

private theorem prime_ninetyNineCS_4987 : Nat.Prime 4987 := by norm_num

private theorem prime_ninetyNineCS_5039 : Nat.Prime 5039 := by norm_num

private theorem prime_ninetyNineCS_5051 : Nat.Prime 5051 := by norm_num

private theorem prime_ninetyNineCS_5087 : Nat.Prime 5087 := by norm_num

private theorem prime_ninetyNineCS_5179 : Nat.Prime 5179 := by norm_num

private theorem prime_ninetyNineCS_5351 : Nat.Prime 5351 := by norm_num

private theorem prime_ninetyNineCS_5399 : Nat.Prime 5399 := by norm_num

private theorem prime_ninetyNineCS_5413 : Nat.Prime 5413 := by norm_num

private theorem prime_ninetyNineCS_5477 : Nat.Prime 5477 := by norm_num

private theorem prime_ninetyNineCS_5507 : Nat.Prime 5507 := by norm_num

private theorem prime_ninetyNineCS_5563 : Nat.Prime 5563 := by norm_num

private theorem prime_ninetyNineCS_5669 : Nat.Prime 5669 := by norm_num

private theorem prime_ninetyNineCS_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_ninetyNineCS_5981 : Nat.Prime 5981 := by norm_num

private theorem prime_ninetyNineCS_6091 : Nat.Prime 6091 := by norm_num

private theorem prime_ninetyNineCS_6131 : Nat.Prime 6131 := by norm_num

private theorem prime_ninetyNineCS_6301 : Nat.Prime 6301 := by norm_num

private theorem prime_ninetyNineCS_6361 : Nat.Prime 6361 := by norm_num

private theorem prime_ninetyNineCS_6637 : Nat.Prime 6637 := by norm_num

private theorem prime_ninetyNineCS_6703 : Nat.Prime 6703 := by norm_num

private theorem prime_ninetyNineCS_6841 : Nat.Prime 6841 := by norm_num

private theorem prime_ninetyNineCS_7703 : Nat.Prime 7703 := by norm_num

private theorem prime_ninetyNineCS_7867 : Nat.Prime 7867 := by norm_num

private theorem prime_ninetyNineCS_8171 : Nat.Prime 8171 := by norm_num

private theorem prime_ninetyNineCS_8291 : Nat.Prime 8291 := by norm_num

private theorem prime_ninetyNineCS_8377 : Nat.Prime 8377 := by norm_num

private theorem prime_ninetyNineCS_9787 : Nat.Prime 9787 := by norm_num

private theorem prime_ninetyNineCS_10267 : Nat.Prime 10267 := by norm_num

private theorem prime_ninetyNineCS_10501 : Nat.Prime 10501 := by norm_num

private theorem prime_ninetyNineCS_11161 : Nat.Prime 11161 := by norm_num

private theorem prime_ninetyNineCS_11317 : Nat.Prime 11317 := by norm_num

private theorem prime_ninetyNineCS_11519 : Nat.Prime 11519 := by norm_num

private theorem prime_ninetyNineCS_11587 : Nat.Prime 11587 := by norm_num

private theorem prime_ninetyNineCS_12263 : Nat.Prime 12263 := by norm_num

private theorem prime_ninetyNineCS_12437 : Nat.Prime 12437 := by norm_num

private theorem prime_ninetyNineCS_12889 : Nat.Prime 12889 := by norm_num

private theorem prime_ninetyNineCS_13147 : Nat.Prime 13147 := by norm_num

private theorem prime_ninetyNineCS_13297 : Nat.Prime 13297 := by norm_num

private theorem prime_ninetyNineCS_13469 : Nat.Prime 13469 := by norm_num

private theorem prime_ninetyNineCS_13729 : Nat.Prime 13729 := by norm_num

private theorem prime_ninetyNineCS_13757 : Nat.Prime 13757 := by norm_num

private theorem prime_ninetyNineCS_14449 : Nat.Prime 14449 := by norm_num

private theorem prime_ninetyNineCS_15017 : Nat.Prime 15017 := by norm_num

private theorem prime_ninetyNineCS_15101 : Nat.Prime 15101 := by norm_num

private theorem prime_ninetyNineCS_15227 : Nat.Prime 15227 := by norm_num

private theorem prime_ninetyNineCS_16187 : Nat.Prime 16187 := by norm_num

private theorem prime_ninetyNineCS_16301 : Nat.Prime 16301 := by norm_num

private theorem prime_ninetyNineCS_16603 : Nat.Prime 16603 := by norm_num

private theorem prime_ninetyNineCS_17327 : Nat.Prime 17327 := by norm_num

private theorem prime_ninetyNineCS_17657 : Nat.Prime 17657 := by norm_num

private theorem prime_ninetyNineCS_17737 : Nat.Prime 17737 := by norm_num

private theorem prime_ninetyNineCS_17971 : Nat.Prime 17971 := by norm_num

private theorem prime_ninetyNineCS_18043 : Nat.Prime 18043 := by norm_num

private theorem prime_ninetyNineCS_18371 : Nat.Prime 18371 := by norm_num

private theorem prime_ninetyNineCS_18461 : Nat.Prime 18461 := by norm_num

private theorem prime_ninetyNineCS_19211 : Nat.Prime 19211 := by norm_num

private theorem prime_ninetyNineCS_21211 : Nat.Prime 21211 := by norm_num

private theorem prime_ninetyNineCS_22367 : Nat.Prime 22367 := by norm_num

private theorem prime_ninetyNineCS_22751 : Nat.Prime 22751 := by norm_num

private theorem prime_ninetyNineCS_23017 : Nat.Prime 23017 := by norm_num

private theorem prime_ninetyNineCS_24623 : Nat.Prime 24623 := by norm_num

private theorem prime_ninetyNineCS_24943 : Nat.Prime 24943 := by norm_num

private theorem prime_ninetyNineCS_25121 : Nat.Prime 25121 := by norm_num

private theorem prime_ninetyNineCS_25229 : Nat.Prime 25229 := by norm_num

private theorem prime_ninetyNineCS_25237 : Nat.Prime 25237 := by norm_num

private theorem prime_ninetyNineCS_25253 : Nat.Prime 25253 := by norm_num

private theorem prime_ninetyNineCS_25667 : Nat.Prime 25667 := by norm_num

private theorem prime_ninetyNineCS_25693 : Nat.Prime 25693 := by norm_num

private theorem prime_ninetyNineCS_25793 : Nat.Prime 25793 := by norm_num

private theorem prime_ninetyNineCS_26783 : Nat.Prime 26783 := by norm_num

private theorem prime_ninetyNineCS_27737 : Nat.Prime 27737 := by norm_num

private theorem prime_ninetyNineCS_27827 : Nat.Prime 27827 := by norm_num

private theorem prime_ninetyNineCS_27953 : Nat.Prime 27953 := by norm_num

private theorem prime_ninetyNineCS_28627 : Nat.Prime 28627 := by norm_num

private theorem prime_ninetyNineCS_29483 : Nat.Prime 29483 := by norm_num

private theorem prime_ninetyNineCS_29587 : Nat.Prime 29587 := by norm_num

private theorem prime_ninetyNineCS_29611 : Nat.Prime 29611 := by norm_num

private theorem prime_ninetyNineCS_29671 : Nat.Prime 29671 := by norm_num

private theorem prime_ninetyNineCS_31253 : Nat.Prime 31253 := by norm_num

private theorem prime_ninetyNineCS_32429 : Nat.Prime 32429 := by norm_num

private theorem prime_ninetyNineCS_33211 : Nat.Prime 33211 := by norm_num

private theorem prime_ninetyNineCS_35801 : Nat.Prime 35801 := by norm_num

private theorem prime_ninetyNineCS_37423 : Nat.Prime 37423 := by norm_num

private theorem prime_ninetyNineCS_38603 : Nat.Prime 38603 := by norm_num

private theorem prime_ninetyNineCS_39451 : Nat.Prime 39451 := by norm_num

private theorem prime_ninetyNineCS_39511 : Nat.Prime 39511 := by norm_num

private theorem prime_ninetyNineCS_39971 : Nat.Prime 39971 := by norm_num

private theorem prime_ninetyNineCS_40903 : Nat.Prime 40903 := by norm_num

private theorem prime_ninetyNineCS_41113 : Nat.Prime 41113 := by norm_num

private theorem prime_ninetyNineCS_41641 : Nat.Prime 41641 := by norm_num

private theorem prime_ninetyNineCS_42089 : Nat.Prime 42089 := by norm_num

private theorem prime_ninetyNineCS_42139 : Nat.Prime 42139 := by norm_num

private theorem prime_ninetyNineCS_43037 : Nat.Prime 43037 := by norm_num

private theorem prime_ninetyNineCS_45319 : Nat.Prime 45319 := by norm_num

private theorem prime_ninetyNineCS_46181 : Nat.Prime 46181 := by norm_num

private theorem prime_ninetyNineCS_46237 : Nat.Prime 46237 := by norm_num

private theorem prime_ninetyNineCS_46439 : Nat.Prime 46439 := by norm_num

private theorem prime_ninetyNineCS_46507 : Nat.Prime 46507 := by norm_num

private theorem prime_ninetyNineCS_46817 : Nat.Prime 46817 := by norm_num

private theorem prime_ninetyNineCS_47527 : Nat.Prime 47527 := by norm_num

private theorem prime_ninetyNineCS_53113 : Nat.Prime 53113 := by norm_num

private theorem prime_ninetyNineCS_53267 : Nat.Prime 53267 := by norm_num

private theorem prime_ninetyNineCS_53441 : Nat.Prime 53441 := by norm_num

private theorem prime_ninetyNineCS_55103 : Nat.Prime 55103 := by norm_num

private theorem prime_ninetyNineCS_57107 : Nat.Prime 57107 := by norm_num

private theorem prime_ninetyNineCS_59707 : Nat.Prime 59707 := by norm_num

private theorem prime_ninetyNineCS_60443 : Nat.Prime 60443 := by norm_num

private theorem prime_ninetyNineCS_62761 : Nat.Prime 62761 := by norm_num

private theorem prime_ninetyNineCS_63317 : Nat.Prime 63317 := by norm_num

private theorem prime_ninetyNineCS_66347 : Nat.Prime 66347 := by norm_num

private theorem prime_ninetyNineCS_66467 : Nat.Prime 66467 := by norm_num

private theorem prime_ninetyNineCS_70003 : Nat.Prime 70003 := by norm_num

private theorem prime_ninetyNineCS_72461 : Nat.Prime 72461 := by norm_num

private theorem prime_ninetyNineCS_74093 : Nat.Prime 74093 := by norm_num

private theorem prime_ninetyNineCS_82193 : Nat.Prime 82193 := by norm_num

private theorem prime_ninetyNineCS_84631 : Nat.Prime 84631 := by norm_num

private theorem prime_ninetyNineCS_87977 : Nat.Prime 87977 := by norm_num

private theorem prime_ninetyNineCS_93739 : Nat.Prime 93739 := by norm_num

private theorem prime_ninetyNineCS_93889 : Nat.Prime 93889 := by norm_num

private theorem prime_ninetyNineCS_108727 : Nat.Prime 108727 := by norm_num

private theorem prime_ninetyNineCS_116381 : Nat.Prime 116381 := by norm_num

private theorem prime_ninetyNineCS_121501 : Nat.Prime 121501 := by norm_num

private theorem prime_ninetyNineCS_154927 : Nat.Prime 154927 := by norm_num

private theorem prime_ninetyNineCS_159491 : Nat.Prime 159491 := by norm_num

private theorem prime_ninetyNineCS_163199 : Nat.Prime 163199 := by norm_num

private theorem prime_ninetyNineCS_175859 : Nat.Prime 175859 := by norm_num

private theorem prime_ninetyNineCS_178021 : Nat.Prime 178021 := by norm_num

private theorem prime_ninetyNineCS_182467 : Nat.Prime 182467 := by norm_num

private theorem prime_ninetyNineCS_196159 : Nat.Prime 196159 := by norm_num

private theorem prime_ninetyNineCS_196727 : Nat.Prime 196727 := by norm_num

private theorem prime_ninetyNineCS_210097 : Nat.Prime 210097 := by norm_num

private theorem prime_ninetyNineCS_221717 : Nat.Prime 221717 := by norm_num

private theorem prime_ninetyNineCS_227653 : Nat.Prime 227653 := by norm_num

private theorem prime_ninetyNineCS_227743 : Nat.Prime 227743 := by norm_num

private theorem prime_ninetyNineCS_230369 : Nat.Prime 230369 := by norm_num

private theorem prime_ninetyNineCS_239963 : Nat.Prime 239963 := by norm_num

private theorem prime_ninetyNineCS_243403 : Nat.Prime 243403 := by norm_num

private theorem prime_ninetyNineCS_252151 : Nat.Prime 252151 := by norm_num

private theorem prime_ninetyNineCS_266449 : Nat.Prime 266449 := by norm_num

private theorem prime_ninetyNineCS_275453 : Nat.Prime 275453 := by norm_num

private theorem prime_ninetyNineCS_290471 : Nat.Prime 290471 := by norm_num

private theorem prime_ninetyNineCS_298759 : Nat.Prime 298759 := by norm_num

private theorem prime_ninetyNineCS_299401 : Nat.Prime 299401 := by norm_num

private theorem prime_ninetyNineCS_328781 : Nat.Prime 328781 := by norm_num

private theorem prime_ninetyNineCS_329309 : Nat.Prime 329309 := by norm_num

private theorem prime_ninetyNineCS_330131 : Nat.Prime 330131 := by norm_num

private theorem prime_ninetyNineCS_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_ninetyNineCS_355573 : Nat.Prime 355573 := by norm_num

private theorem prime_ninetyNineCS_385261 : Nat.Prime 385261 := by norm_num

private theorem prime_ninetyNineCS_395261 : Nat.Prime 395261 := by norm_num

private theorem prime_ninetyNineCS_397057 : Nat.Prime 397057 := by norm_num

private theorem prime_ninetyNineCS_397897 : Nat.Prime 397897 := by norm_num

private theorem prime_ninetyNineCS_427379 : Nat.Prime 427379 := by norm_num

private theorem prime_ninetyNineCS_446179 : Nat.Prime 446179 := by norm_num

private theorem prime_ninetyNineCS_484303 : Nat.Prime 484303 := by norm_num

private theorem prime_ninetyNineCS_509449 : Nat.Prime 509449 := by norm_num

private theorem prime_ninetyNineCS_534029 : Nat.Prime 534029 := by norm_num

private theorem prime_ninetyNineCS_574373 : Nat.Prime 574373 := by norm_num

private theorem prime_ninetyNineCS_580969 : Nat.Prime 580969 := by norm_num

private theorem prime_ninetyNineCS_600371 : Nat.Prime 600371 := by norm_num

private theorem prime_ninetyNineCS_612649 : Nat.Prime 612649 := by norm_num

private theorem prime_ninetyNineCS_647201 : Nat.Prime 647201 := by norm_num

private theorem prime_ninetyNineCS_683899 : Nat.Prime 683899 := by norm_num

private theorem prime_ninetyNineCS_730421 : Nat.Prime 730421 := by norm_num

private theorem prime_ninetyNineCS_838421 : Nat.Prime 838421 := by norm_num

private theorem prime_ninetyNineCS_873641 : Nat.Prime 873641 := by norm_num

private theorem prime_ninetyNineCS_889367 : Nat.Prime 889367 := by norm_num

private theorem prime_ninetyNineCS_897647 : Nat.Prime 897647 := by norm_num

private theorem prime_ninetyNineCS_903037 : Nat.Prime 903037 := by norm_num

private theorem prime_ninetyNineCS_940031 : Nat.Prime 940031 := by norm_num

private theorem prime_ninetyNineCS_996571 : Nat.Prime 996571 := by norm_num

private theorem prime_ninetyNineCS_1039001 : Nat.Prime 1039001 := by norm_num

private theorem prime_ninetyNineCS_1073399 : Nat.Prime 1073399 := by norm_num

private theorem prime_ninetyNineCS_1115321 : Nat.Prime 1115321 := by norm_num

private theorem prime_ninetyNineCS_1218571 : Nat.Prime 1218571 := by norm_num

private theorem prime_ninetyNineCS_1254497 : Nat.Prime 1254497 := by norm_num

private theorem prime_ninetyNineCS_1332949 : Nat.Prime 1332949 := by norm_num

private theorem prime_ninetyNineCS_1359509 : Nat.Prime 1359509 := by norm_num

private theorem prime_ninetyNineCS_1377469 : Nat.Prime 1377469 := by norm_num

private theorem prime_ninetyNineCS_1423759 : Nat.Prime 1423759 := by norm_num

private theorem prime_ninetyNineCS_1430713 : Nat.Prime 1430713 := by norm_num

private theorem prime_ninetyNineCS_1437187 : Nat.Prime 1437187 := by norm_num

private theorem prime_ninetyNineCS_1537639 : Nat.Prime 1537639 := by norm_num

private theorem prime_ninetyNineCS_1617019 : Nat.Prime 1617019 := by norm_num

private theorem prime_ninetyNineCS_1624423 : Nat.Prime 1624423 := by norm_num

private theorem prime_ninetyNineCS_1769771 : Nat.Prime 1769771 := by norm_num

private theorem prime_ninetyNineCS_1824073 : Nat.Prime 1824073 := by norm_num

private theorem prime_ninetyNineCS_1875943 : Nat.Prime 1875943 := by norm_num

private theorem prime_ninetyNineCS_2002339 : Nat.Prime 2002339 := by norm_num

private theorem prime_ninetyNineCS_2084903 : Nat.Prime 2084903 := by norm_num

private theorem prime_ninetyNineCS_2105273 : Nat.Prime 2105273 := by norm_num

private theorem prime_ninetyNineCS_2218609 : Nat.Prime 2218609 := by norm_num

private theorem prime_ninetyNineCS_2289193 : Nat.Prime 2289193 := by norm_num

private theorem prime_ninetyNineCS_2555731 : Nat.Prime 2555731 := by norm_num

private theorem prime_ninetyNineCS_2746801 : Nat.Prime 2746801 := by norm_num

private theorem prime_ninetyNineCS_2769443 : Nat.Prime 2769443 := by norm_num

private theorem prime_ninetyNineCS_2906663 : Nat.Prime 2906663 := by norm_num

private theorem prime_ninetyNineCS_2987297 : Nat.Prime 2987297 := by norm_num

private theorem prime_ninetyNineCS_3258487 : Nat.Prime 3258487 := by norm_num

private theorem prime_ninetyNineCS_3401807 : Nat.Prime 3401807 := by norm_num

private theorem prime_ninetyNineCS_3470113 : Nat.Prime 3470113 := by norm_num

private theorem prime_ninetyNineCS_3563653 : Nat.Prime 3563653 := by norm_num

private theorem prime_ninetyNineCS_3650791 : Nat.Prime 3650791 := by norm_num

private theorem prime_ninetyNineCS_3676193 : Nat.Prime 3676193 := by norm_num

private theorem prime_ninetyNineCS_3766073 : Nat.Prime 3766073 := by norm_num

private theorem prime_ninetyNineCS_3777883 : Nat.Prime 3777883 := by norm_num

private theorem prime_ninetyNineCS_3803879 : Nat.Prime 3803879 := by norm_num

private theorem prime_ninetyNineCS_3855793 : Nat.Prime 3855793 := by norm_num

private theorem prime_ninetyNineCS_4035601 : Nat.Prime 4035601 := by norm_num

private theorem prime_ninetyNineCS_4053503 : Nat.Prime 4053503 := by norm_num

private theorem prime_ninetyNineCS_4119937 : Nat.Prime 4119937 := by norm_num

private theorem prime_ninetyNineCS_4128743 : Nat.Prime 4128743 := by norm_num

private theorem prime_ninetyNineCS_4228313 : Nat.Prime 4228313 := by norm_num

private theorem prime_ninetyNineCS_4240079 : Nat.Prime 4240079 := by norm_num

private theorem prime_ninetyNineCS_4280153 : Nat.Prime 4280153 := by norm_num

private theorem prime_ninetyNineCS_4353967 : Nat.Prime 4353967 := by norm_num

private theorem prime_ninetyNineCS_4430507 : Nat.Prime 4430507 := by norm_num

private theorem prime_ninetyNineCS_4859249 : Nat.Prime 4859249 := by norm_num

private theorem prime_ninetyNineCS_4886501 : Nat.Prime 4886501 := by norm_num

private theorem prime_ninetyNineCS_5082691 : Nat.Prime 5082691 := by norm_num

private theorem prime_ninetyNineCS_5142107 : Nat.Prime 5142107 := by norm_num

private theorem prime_ninetyNineCS_5153647 : Nat.Prime 5153647 := by norm_num

private theorem prime_ninetyNineCS_5415691 : Nat.Prime 5415691 := by norm_num

private theorem prime_ninetyNineCS_5800019 : Nat.Prime 5800019 := by norm_num

private theorem prime_ninetyNineCS_5902649 : Nat.Prime 5902649 := by norm_num

private theorem prime_ninetyNineCS_6081139 : Nat.Prime 6081139 := by norm_num

private theorem prime_ninetyNineCS_6186979 : Nat.Prime 6186979 := by norm_num

private theorem prime_ninetyNineCS_6203573 : Nat.Prime 6203573 := by norm_num

private theorem prime_ninetyNineCS_6395833 : Nat.Prime 6395833 := by norm_num

private theorem prime_ninetyNineCS_7458931 : Nat.Prime 7458931 := by norm_num

private theorem prime_ninetyNineCS_7508843 : Nat.Prime 7508843 := by norm_num

private theorem prime_ninetyNineCS_8408143 : Nat.Prime 8408143 := by norm_num

private theorem prime_ninetyNineCS_8649803 : Nat.Prime 8649803 := by norm_num

private theorem prime_ninetyNineCS_8658847 : Nat.Prime 8658847 := by norm_num

private theorem prime_ninetyNineCS_9540121 : Nat.Prime 9540121 := by norm_num

private theorem prime_ninetyNineCS_9649667 : Nat.Prime 9649667 := by norm_num

private theorem prime_ninetyNineCS_9655267 : Nat.Prime 9655267 := by norm_num

private theorem prime_ninetyNineCS_9668369 : Nat.Prime 9668369 := by norm_num

private theorem prime_ninetyNineCS_11638213 : Nat.Prime 11638213 := by norm_num

private theorem prime_ninetyNineCS_11883769 : Nat.Prime 11883769 := by norm_num

private theorem prime_ninetyNineCS_11963327 : Nat.Prime 11963327 := by norm_num

private theorem prime_ninetyNineCS_12009997 : Nat.Prime 12009997 := by norm_num

private theorem prime_ninetyNineCS_12251719 : Nat.Prime 12251719 := by norm_num

private theorem prime_ninetyNineCS_12810799 : Nat.Prime 12810799 := by norm_num

private theorem prime_ninetyNineCS_13046347 : Nat.Prime 13046347 := by norm_num

private theorem prime_ninetyNineCS_13458461 : Nat.Prime 13458461 := by norm_num

private theorem prime_ninetyNineCS_13970287 : Nat.Prime 13970287 := by norm_num

private theorem prime_ninetyNineCS_14178851 : Nat.Prime 14178851 := by norm_num

private theorem prime_ninetyNineCS_14248447 : Nat.Prime 14248447 := by norm_num

private theorem prime_ninetyNineCS_15728017 : Nat.Prime 15728017 := by norm_num

private theorem prime_ninetyNineCS_18703511 : Nat.Prime 18703511 := by norm_num

private theorem prime_ninetyNineCS_18808877 : Nat.Prime 18808877 := by norm_num

private theorem prime_ninetyNineCS_20289103 : Nat.Prime 20289103 := by norm_num

private theorem prime_ninetyNineCS_20637497 : Nat.Prime 20637497 := by norm_num

private theorem prime_ninetyNineCS_21818921 : Nat.Prime 21818921 := by norm_num

private theorem prime_ninetyNineCS_24904889 : Nat.Prime 24904889 := by norm_num

private theorem prime_ninetyNineCS_25129453 : Nat.Prime 25129453 := by norm_num

private theorem prime_ninetyNineCS_25305101 : Nat.Prime 25305101 := by norm_num

private theorem prime_ninetyNineCS_26143727 : Nat.Prime 26143727 := by norm_num

private theorem prime_ninetyNineCS_28331507 : Nat.Prime 28331507 := by norm_num

private theorem prime_ninetyNineCS_29380409 : Nat.Prime 29380409 := by norm_num

private theorem prime_ninetyNineCS_31322699 : Nat.Prime 31322699 := by
  apply lucas_primality 31322699 (2 : ZMod 31322699)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1423759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1423759, 1)] : List FactorBlock).map factorBlockValue).prod) = 31322699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_1423759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31322699) ^ 15661349 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 31322699) ^ 2847518 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 31322699) ^ 22 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_32315293 : Nat.Prime 32315293 := by
  apply lucas_primality 32315293 (2 : ZMod 32315293)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (897647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (897647, 1)] : List FactorBlock).map factorBlockValue).prod) = 32315293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_897647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32315293) ^ 16157646 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 32315293) ^ 10771764 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 32315293) ^ 36 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_34635389 : Nat.Prime 34635389 := by
  apply lucas_primality 34635389 (2 : ZMod 34635389)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8658847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8658847, 1)] : List FactorBlock).map factorBlockValue).prod) = 34635389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_8658847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 34635389) ^ 17317694 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 34635389) ^ 4 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_37488523 : Nat.Prime 37488523 := by
  apply lucas_primality 37488523 (2 : ZMod 37488523)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1237, 1), (5051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1237, 1), (5051, 1)] : List FactorBlock).map factorBlockValue).prod) = 37488523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_1237
      · exact prime_ninetyNineCS_5051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37488523) ^ 18744261 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 37488523) ^ 12496174 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 37488523) ^ 30306 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 37488523) ^ 7422 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_37634911 : Nat.Prime 37634911 := by
  apply lucas_primality 37634911 (15 : ZMod 37634911)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1254497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1254497, 1)] : List FactorBlock).map factorBlockValue).prod) = 37634911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_1254497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 37634911) ^ 18817455 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (15 : ZMod 37634911) ^ 12544970 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (15 : ZMod 37634911) ^ 7526982 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (15 : ZMod 37634911) ^ 30 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_40789163 : Nat.Prime 40789163 := by
  apply lucas_primality 40789163 (2 : ZMod 40789163)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1073399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1073399, 1)] : List FactorBlock).map factorBlockValue).prod) = 40789163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_1073399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40789163) ^ 20394581 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 40789163) ^ 2146798 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 40789163) ^ 38 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_42473047 : Nat.Prime 42473047 := by
  apply lucas_primality 42473047 (5 : ZMod 42473047)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (149, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (149, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 42473047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_149
      · exact prime_ninetyNineCS_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 42473047) ^ 21236523 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 42473047) ^ 14157682 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 42473047) ^ 6067578 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 42473047) ^ 3861186 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 42473047) ^ 285054 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 42473047) ^ 68838 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_44574419 : Nat.Prime 44574419 := by
  apply lucas_primality 44574419 (2 : ZMod 44574419)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (19, 1), (37, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (19, 1), (37, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 44574419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_37
      · exact prime_ninetyNineCS_647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44574419) ^ 22287209 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44574419) ^ 6367774 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44574419) ^ 2346022 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44574419) ^ 1204714 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44574419) ^ 68894 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_44936009 : Nat.Prime 44936009 := by
  apply lucas_primality 44936009 (3 : ZMod 44936009)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (503, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (503, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) = 44936009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_503
      · exact prime_ninetyNineCS_859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 44936009) ^ 22468004 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 44936009) ^ 3456616 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 44936009) ^ 89336 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 44936009) ^ 52312 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_48571751 : Nat.Prime 48571751 := by
  apply lucas_primality 48571751 (7 : ZMod 48571751)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (37, 1), (59, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (37, 1), (59, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 48571751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_37
      · exact prime_ninetyNineCS_59
      · exact prime_ninetyNineCS_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 48571751) ^ 24285875 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 48571751) ^ 9714350 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 48571751) ^ 1312750 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 48571751) ^ 823250 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 48571751) ^ 545750 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_50437169 : Nat.Prime 50437169 := by
  apply lucas_primality 50437169 (3 : ZMod 50437169)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1301, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1301, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) = 50437169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_1301
      · exact prime_ninetyNineCS_2423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 50437169) ^ 25218584 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 50437169) ^ 38768 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 50437169) ^ 20816 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_51449579 : Nat.Prime 51449579 := by
  apply lucas_primality 51449579 (2 : ZMod 51449579)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (227653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (227653, 1)] : List FactorBlock).map factorBlockValue).prod) = 51449579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_113
      · exact prime_ninetyNineCS_227653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 51449579) ^ 25724789 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 51449579) ^ 455306 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 51449579) ^ 226 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_53362021 : Nat.Prime 53362021 := by
  apply lucas_primality 53362021 (2 : ZMod 53362021)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (889367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (889367, 1)] : List FactorBlock).map factorBlockValue).prod) = 53362021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_889367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53362021) ^ 26681010 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 53362021) ^ 17787340 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 53362021) ^ 10672404 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 53362021) ^ 60 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_56993789 : Nat.Prime 56993789 := by
  apply lucas_primality 56993789 (2 : ZMod 56993789)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14248447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14248447, 1)] : List FactorBlock).map factorBlockValue).prod) = 56993789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_14248447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 56993789) ^ 28496894 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 56993789) ^ 4 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_58652767 : Nat.Prime 58652767 := by
  apply lucas_primality 58652767 (3 : ZMod 58652767)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3258487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3258487, 1)] : List FactorBlock).map factorBlockValue).prod) = 58652767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_3258487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 58652767) ^ 29326383 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 58652767) ^ 19550922 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 58652767) ^ 18 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_59258839 : Nat.Prime 59258839 := by
  apply lucas_primality 59258839 (3 : ZMod 59258839)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (580969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (580969, 1)] : List FactorBlock).map factorBlockValue).prod) = 59258839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_580969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59258839) ^ 29629419 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 59258839) ^ 19752946 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 59258839) ^ 3485814 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 59258839) ^ 102 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_61039241 : Nat.Prime 61039241 := by
  apply lucas_primality 61039241 (3 : ZMod 61039241)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (66347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (66347, 1)] : List FactorBlock).map factorBlockValue).prod) = 61039241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_23
      · exact prime_ninetyNineCS_66347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 61039241) ^ 30519620 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 61039241) ^ 12207848 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 61039241) ^ 2653880 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 61039241) ^ 920 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_67127519 : Nat.Prime 67127519 := by
  apply lucas_primality 67127519 (7 : ZMod 67127519)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (71, 1), (16301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (71, 1), (16301, 1)] : List FactorBlock).map factorBlockValue).prod) = 67127519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_29
      · exact prime_ninetyNineCS_71
      · exact prime_ninetyNineCS_16301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 67127519) ^ 33563759 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 67127519) ^ 2314742 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 67127519) ^ 945458 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 67127519) ^ 4118 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_71045453 : Nat.Prime 71045453 := by
  apply lucas_primality 71045453 (2 : ZMod 71045453)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (283, 1), (62761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (283, 1), (62761, 1)] : List FactorBlock).map factorBlockValue).prod) = 71045453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_283
      · exact prime_ninetyNineCS_62761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 71045453) ^ 35522726 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 71045453) ^ 251044 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 71045453) ^ 1132 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_75133127 : Nat.Prime 75133127 := by
  apply lucas_primality 75133127 (5 : ZMod 75133127)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (873641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (873641, 1)] : List FactorBlock).map factorBlockValue).prod) = 75133127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_43
      · exact prime_ninetyNineCS_873641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 75133127) ^ 37566563 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 75133127) ^ 1747282 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 75133127) ^ 86 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_76067083 : Nat.Prime 76067083 := by
  apply lucas_primality 76067083 (5 : ZMod 76067083)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (46439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (46439, 1)] : List FactorBlock).map factorBlockValue).prod) = 76067083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_46439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 76067083) ^ 38033541 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 76067083) ^ 25355694 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 76067083) ^ 10866726 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 76067083) ^ 5851314 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 76067083) ^ 1638 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_76910429 : Nat.Prime 76910429 := by
  apply lucas_primality 76910429 (2 : ZMod 76910429)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2746801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2746801, 1)] : List FactorBlock).map factorBlockValue).prod) = 76910429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_2746801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 76910429) ^ 38455214 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 76910429) ^ 10987204 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 76910429) ^ 28 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_80038859 : Nat.Prime 80038859 := by
  apply lucas_primality 80038859 (2 : ZMod 80038859)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5087, 1), (7867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5087, 1), (7867, 1)] : List FactorBlock).map factorBlockValue).prod) = 80038859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5087
      · exact prime_ninetyNineCS_7867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 80038859) ^ 40019429 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 80038859) ^ 15734 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 80038859) ^ 10174 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_86231221 : Nat.Prime 86231221 := by
  apply lucas_primality 86231221 (6 : ZMod 86231221)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1437187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1437187, 1)] : List FactorBlock).map factorBlockValue).prod) = 86231221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_1437187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 86231221) ^ 43115610 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 86231221) ^ 28743740 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 86231221) ^ 17246244 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 86231221) ^ 60 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_89857661 : Nat.Prime 89857661 := by
  apply lucas_primality 89857661 (3 : ZMod 89857661)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (154927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (154927, 1)] : List FactorBlock).map factorBlockValue).prod) = 89857661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_29
      · exact prime_ninetyNineCS_154927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 89857661) ^ 44928830 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 89857661) ^ 17971532 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 89857661) ^ 3098540 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 89857661) ^ 580 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_89872019 : Nat.Prime 89872019 := by
  apply lucas_primality 89872019 (2 : ZMod 89872019)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (44936009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (44936009, 1)] : List FactorBlock).map factorBlockValue).prod) = 89872019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_44936009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 89872019) ^ 44936009 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 89872019) ^ 2 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_93348407 : Nat.Prime 93348407 := by
  apply lucas_primality 93348407 (5 : ZMod 93348407)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (251, 1), (9787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (251, 1), (9787, 1)] : List FactorBlock).map factorBlockValue).prod) = 93348407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_251
      · exact prime_ninetyNineCS_9787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 93348407) ^ 46674203 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 93348407) ^ 4913074 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 93348407) ^ 371906 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 93348407) ^ 9538 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_94061897 : Nat.Prime 94061897 := by
  apply lucas_primality 94061897 (3 : ZMod 94061897)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (439, 1), (26783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (439, 1), (26783, 1)] : List FactorBlock).map factorBlockValue).prod) = 94061897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_439
      · exact prime_ninetyNineCS_26783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 94061897) ^ 47030948 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 94061897) ^ 214264 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 94061897) ^ 3512 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_97143503 : Nat.Prime 97143503 := by
  apply lucas_primality 97143503 (5 : ZMod 97143503)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (48571751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (48571751, 1)] : List FactorBlock).map factorBlockValue).prod) = 97143503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_48571751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 97143503) ^ 48571751 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 97143503) ^ 2 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_104482753 : Nat.Prime 104482753 := by
  apply lucas_primality 104482753 (13 : ZMod 104482753)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 1), (61, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 1), (61, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 104482753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_61
      · exact prime_ninetyNineCS_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 104482753) ^ 52241376 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 104482753) ^ 34827584 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 104482753) ^ 9498432 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 104482753) ^ 1712832 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 104482753) ^ 128832 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_109891261 : Nat.Prime 109891261 := by
  apply lucas_primality 109891261 (6 : ZMod 109891261)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (53, 1), (11519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (53, 1), (11519, 1)] : List FactorBlock).map factorBlockValue).prod) = 109891261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_53
      · exact prime_ninetyNineCS_11519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 109891261) ^ 54945630 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 109891261) ^ 36630420 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 109891261) ^ 21978252 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 109891261) ^ 2073420 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 109891261) ^ 9540 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_114481453 : Nat.Prime 114481453 := by
  apply lucas_primality 114481453 (2 : ZMod 114481453)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (9540121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (9540121, 1)] : List FactorBlock).map factorBlockValue).prod) = 114481453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_9540121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 114481453) ^ 57240726 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 114481453) ^ 38160484 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 114481453) ^ 12 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_136113539 : Nat.Prime 136113539 := by
  apply lucas_primality 136113539 (2 : ZMod 136113539)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (6186979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (6186979, 1)] : List FactorBlock).map factorBlockValue).prod) = 136113539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_6186979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 136113539) ^ 68056769 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 136113539) ^ 12373958 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 136113539) ^ 22 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_144236189 : Nat.Prime 144236189 := by
  apply lucas_primality 144236189 (2 : ZMod 144236189)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1877, 1), (19211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1877, 1), (19211, 1)] : List FactorBlock).map factorBlockValue).prod) = 144236189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_1877
      · exact prime_ninetyNineCS_19211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144236189) ^ 72118094 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236189) ^ 76844 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 144236189) ^ 7508 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_152969081 : Nat.Prime 152969081 := by
  apply lucas_primality 152969081 (7 : ZMod 152969081)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (223, 1), (1559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (223, 1), (1559, 1)] : List FactorBlock).map factorBlockValue).prod) = 152969081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_223
      · exact prime_ninetyNineCS_1559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 152969081) ^ 76484540 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 152969081) ^ 30593816 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 152969081) ^ 13906280 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 152969081) ^ 685960 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 152969081) ^ 98120 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_158531911 : Nat.Prime 158531911 := by
  apply lucas_primality 158531911 (13 : ZMod 158531911)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (73, 1), (191, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (73, 1), (191, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) = 158531911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_73
      · exact prime_ninetyNineCS_191
      · exact prime_ninetyNineCS_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 158531911) ^ 79265955 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 158531911) ^ 52843970 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 158531911) ^ 31706382 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 158531911) ^ 2171670 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 158531911) ^ 830010 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 158531911) ^ 418290 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_159625199 : Nat.Prime 159625199 := by
  apply lucas_primality 159625199 (13 : ZMod 159625199)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (3470113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (3470113, 1)] : List FactorBlock).map factorBlockValue).prod) = 159625199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_23
      · exact prime_ninetyNineCS_3470113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 159625199) ^ 79812599 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 159625199) ^ 6940226 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 159625199) ^ 46 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_183596239 : Nat.Prime 183596239 := by
  apply lucas_primality 183596239 (3 : ZMod 183596239)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 3), (131, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 3), (131, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 183596239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_131
      · exact prime_ninetyNineCS_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 183596239) ^ 91798119 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 183596239) ^ 61198746 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 183596239) ^ 26228034 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 183596239) ^ 1401498 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 183596239) ^ 808794 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_189841133 : Nat.Prime 189841133 := by
  apply lucas_primality 189841133 (2 : ZMod 189841133)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (3650791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (3650791, 1)] : List FactorBlock).map factorBlockValue).prod) = 189841133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_3650791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 189841133) ^ 94920566 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 189841133) ^ 14603164 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 189841133) ^ 52 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_199600837 : Nat.Prime 199600837 := by
  apply lucas_primality 199600837 (5 : ZMod 199600837)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2713, 1), (6131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2713, 1), (6131, 1)] : List FactorBlock).map factorBlockValue).prod) = 199600837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_2713
      · exact prime_ninetyNineCS_6131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 199600837) ^ 99800418 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 199600837) ^ 66533612 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 199600837) ^ 73572 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 199600837) ^ 32556 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_205929949 : Nat.Prime 205929949 := by
  apply lucas_primality 205929949 (6 : ZMod 205929949)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (23, 1), (15227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (23, 1), (15227, 1)] : List FactorBlock).map factorBlockValue).prod) = 205929949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_23
      · exact prime_ninetyNineCS_15227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 205929949) ^ 102964974 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 205929949) ^ 68643316 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 205929949) ^ 29418564 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 205929949) ^ 8953476 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 205929949) ^ 13524 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_216179947 : Nat.Prime 216179947 := by
  apply lucas_primality 216179947 (2 : ZMod 216179947)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (12009997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (12009997, 1)] : List FactorBlock).map factorBlockValue).prod) = 216179947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_12009997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 216179947) ^ 108089973 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 216179947) ^ 72059982 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 216179947) ^ 18 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_217745893 : Nat.Prime 217745893 := by
  apply lucas_primality 217745893 (2 : ZMod 217745893)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (13, 1), (66467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (13, 1), (66467, 1)] : List FactorBlock).map factorBlockValue).prod) = 217745893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_66467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 217745893) ^ 108872946 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 217745893) ^ 72581964 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 217745893) ^ 31106556 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 217745893) ^ 16749684 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 217745893) ^ 3276 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_244951459 : Nat.Prime 244951459 := by
  apply lucas_primality 244951459 (2 : ZMod 244951459)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (29, 1), (74093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (29, 1), (74093, 1)] : List FactorBlock).map factorBlockValue).prod) = 244951459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_29
      · exact prime_ninetyNineCS_74093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 244951459) ^ 122475729 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 244951459) ^ 81650486 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 244951459) ^ 12892182 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 244951459) ^ 8446602 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 244951459) ^ 3306 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_250891343 : Nat.Prime 250891343 := by
  apply lucas_primality 250891343 (5 : ZMod 250891343)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (9649667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (9649667, 1)] : List FactorBlock).map factorBlockValue).prod) = 250891343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_9649667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 250891343) ^ 125445671 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 250891343) ^ 19299334 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 250891343) ^ 26 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_265827713 : Nat.Prime 265827713 := by
  apply lucas_primality 265827713 (3 : ZMod 265827713)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (401, 1), (5179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (401, 1), (5179, 1)] : List FactorBlock).map factorBlockValue).prod) = 265827713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_401
      · exact prime_ninetyNineCS_5179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 265827713) ^ 132913856 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 265827713) ^ 662912 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 265827713) ^ 51328 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_269865733 : Nat.Prime 269865733 := by
  apply lucas_primality 269865733 (2 : ZMod 269865733)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (547, 1), (41113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (547, 1), (41113, 1)] : List FactorBlock).map factorBlockValue).prod) = 269865733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_547
      · exact prime_ninetyNineCS_41113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 269865733) ^ 134932866 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 269865733) ^ 89955244 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 269865733) ^ 493356 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 269865733) ^ 6564 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_299536001 : Nat.Prime 299536001 := by
  apply lucas_primality 299536001 (3 : ZMod 299536001)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 3), (97, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 3), (97, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 299536001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_97
      · exact prime_ninetyNineCS_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 299536001) ^ 149768000 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 299536001) ^ 59907200 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 299536001) ^ 3088000 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 299536001) ^ 1552000 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_387443669 : Nat.Prime 387443669 := by
  apply lucas_primality 387443669 (2 : ZMod 387443669)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (19, 1), (83, 1), (3613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (19, 1), (83, 1), (3613, 1)] : List FactorBlock).map factorBlockValue).prod) = 387443669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_83
      · exact prime_ninetyNineCS_3613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 387443669) ^ 193721834 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 387443669) ^ 22790804 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 387443669) ^ 20391772 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 387443669) ^ 4667996 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 387443669) ^ 107236 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_430464637 : Nat.Prime 430464637 := by
  apply lucas_primality 430464637 (2 : ZMod 430464637)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (31, 1), (55103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (31, 1), (55103, 1)] : List FactorBlock).map factorBlockValue).prod) = 430464637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_55103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 430464637) ^ 215232318 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 430464637) ^ 143488212 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 430464637) ^ 61494948 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 430464637) ^ 13885956 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 430464637) ^ 7812 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_473283353 : Nat.Prime 473283353 := by
  apply lucas_primality 473283353 (3 : ZMod 473283353)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (574373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (574373, 1)] : List FactorBlock).map factorBlockValue).prod) = 473283353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_103
      · exact prime_ninetyNineCS_574373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 473283353) ^ 236641676 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 473283353) ^ 4594984 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 473283353) ^ 824 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_477447643 : Nat.Prime 477447643 := by
  apply lucas_primality 477447643 (5 : ZMod 477447643)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (103, 1), (12263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (103, 1), (12263, 1)] : List FactorBlock).map factorBlockValue).prod) = 477447643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_103
      · exact prime_ninetyNineCS_12263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 477447643) ^ 238723821 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 477447643) ^ 159149214 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 477447643) ^ 68206806 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 477447643) ^ 4635414 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 477447643) ^ 38934 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_489469957 : Nat.Prime 489469957 := by
  apply lucas_primality 489469957 (2 : ZMod 489469957)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (40789163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (40789163, 1)] : List FactorBlock).map factorBlockValue).prod) = 489469957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_40789163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 489469957) ^ 244734978 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 489469957) ^ 163156652 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 489469957) ^ 12 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_489551137 : Nat.Prime 489551137 := by
  apply lucas_primality 489551137 (10 : ZMod 489551137)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (221717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (221717, 1)] : List FactorBlock).map factorBlockValue).prod) = 489551137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_23
      · exact prime_ninetyNineCS_221717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 489551137) ^ 244775568 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 489551137) ^ 163183712 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 489551137) ^ 21284832 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 489551137) ^ 2208 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_531660841 : Nat.Prime 531660841 := by
  apply lucas_primality 531660841 (19 : ZMod 531660841)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (4430507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (4430507, 1)] : List FactorBlock).map factorBlockValue).prod) = 531660841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_4430507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 531660841) ^ 265830420 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (19 : ZMod 531660841) ^ 177220280 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (19 : ZMod 531660841) ^ 106332168 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (19 : ZMod 531660841) ^ 120 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_533620211 : Nat.Prime 533620211 := by
  apply lucas_primality 533620211 (6 : ZMod 533620211)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53362021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53362021, 1)] : List FactorBlock).map factorBlockValue).prod) = 533620211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_53362021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 533620211) ^ 266810105 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 533620211) ^ 106724042 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 533620211) ^ 10 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_620419991 : Nat.Prime 620419991 := by
  apply lucas_primality 620419991 (7 : ZMod 620419991)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (389, 1), (159491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (389, 1), (159491, 1)] : List FactorBlock).map factorBlockValue).prod) = 620419991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_389
      · exact prime_ninetyNineCS_159491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 620419991) ^ 310209995 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 620419991) ^ 124083998 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 620419991) ^ 1594910 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 620419991) ^ 3890 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_655020643 : Nat.Prime 655020643 := by
  apply lucas_primality 655020643 (2 : ZMod 655020643)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (157, 1), (40903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (157, 1), (40903, 1)] : List FactorBlock).map factorBlockValue).prod) = 655020643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_157
      · exact prime_ninetyNineCS_40903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 655020643) ^ 327510321 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 655020643) ^ 218340214 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 655020643) ^ 38530626 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 655020643) ^ 4172106 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 655020643) ^ 16014 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_679736903 : Nat.Prime 679736903 := by
  apply lucas_primality 679736903 (5 : ZMod 679736903)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (26143727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (26143727, 1)] : List FactorBlock).map factorBlockValue).prod) = 679736903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_26143727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 679736903) ^ 339868451 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 679736903) ^ 52287454 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 679736903) ^ 26 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_752072917 : Nat.Prime 752072917 := by
  apply lucas_primality 752072917 (2 : ZMod 752072917)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (2039, 1), (4391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (2039, 1), (4391, 1)] : List FactorBlock).map factorBlockValue).prod) = 752072917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_2039
      · exact prime_ninetyNineCS_4391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 752072917) ^ 376036458 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 752072917) ^ 250690972 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 752072917) ^ 107438988 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 752072917) ^ 368844 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 752072917) ^ 171276 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_764514847 : Nat.Prime 764514847 := by
  apply lucas_primality 764514847 (3 : ZMod 764514847)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (42473047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (42473047, 1)] : List FactorBlock).map factorBlockValue).prod) = 764514847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_42473047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 764514847) ^ 382257423 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 764514847) ^ 254838282 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 764514847) ^ 18 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_845095217 : Nat.Prime 845095217 := by
  apply lucas_primality 845095217 (3 : ZMod 845095217)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (31, 1), (243403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (31, 1), (243403, 1)] : List FactorBlock).map factorBlockValue).prod) = 845095217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_243403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 845095217) ^ 422547608 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 845095217) ^ 120727888 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 845095217) ^ 27261136 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 845095217) ^ 3472 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_983764777 : Nat.Prime 983764777 := by
  apply lucas_primality 983764777 (10 : ZMod 983764777)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1597, 1), (25667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1597, 1), (25667, 1)] : List FactorBlock).map factorBlockValue).prod) = 983764777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_1597
      · exact prime_ninetyNineCS_25667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 983764777) ^ 491882388 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 983764777) ^ 327921592 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 983764777) ^ 616008 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 983764777) ^ 38328 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1034844997 : Nat.Prime 1034844997 := by
  apply lucas_primality 1034844997 (2 : ZMod 1034844997)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (1039001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (1039001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1034844997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_83
      · exact prime_ninetyNineCS_1039001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1034844997) ^ 517422498 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1034844997) ^ 344948332 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1034844997) ^ 12468012 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1034844997) ^ 996 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1062372643 : Nat.Prime 1062372643 := by
  apply lucas_primality 1062372643 (3 : ZMod 1062372643)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (1624423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (1624423, 1)] : List FactorBlock).map factorBlockValue).prod) = 1062372643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_109
      · exact prime_ninetyNineCS_1624423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1062372643) ^ 531186321 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1062372643) ^ 354124214 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1062372643) ^ 9746538 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1062372643) ^ 654 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1150109341 : Nat.Prime 1150109341 := by
  apply lucas_primality 1150109341 (2 : ZMod 1150109341)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1867, 1), (10267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1867, 1), (10267, 1)] : List FactorBlock).map factorBlockValue).prod) = 1150109341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_1867
      · exact prime_ninetyNineCS_10267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1150109341) ^ 575054670 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1150109341) ^ 383369780 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1150109341) ^ 230021868 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1150109341) ^ 616020 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1150109341) ^ 112020 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1212718499 : Nat.Prime 1212718499 := by
  apply lucas_primality 1212718499 (2 : ZMod 1212718499)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (1069, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (1069, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1212718499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_103
      · exact prime_ninetyNineCS_1069
      · exact prime_ninetyNineCS_5507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1212718499) ^ 606359249 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1212718499) ^ 11773966 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1212718499) ^ 1134442 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1212718499) ^ 220214 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1240839983 : Nat.Prime 1240839983 := by
  apply lucas_primality 1240839983 (5 : ZMod 1240839983)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (620419991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (620419991, 1)] : List FactorBlock).map factorBlockValue).prod) = 1240839983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_620419991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1240839983) ^ 620419991 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1240839983) ^ 2 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1303694459 : Nat.Prime 1303694459 := by
  apply lucas_primality 1303694459 (2 : ZMod 1303694459)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (59258839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (59258839, 1)] : List FactorBlock).map factorBlockValue).prod) = 1303694459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_59258839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1303694459) ^ 651847229 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1303694459) ^ 118517678 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1303694459) ^ 22 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1362485191 : Nat.Prime 1362485191 := by
  apply lucas_primality 1362485191 (3 : ZMod 1362485191)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (4128743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (4128743, 1)] : List FactorBlock).map factorBlockValue).prod) = 1362485191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_4128743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1362485191) ^ 681242595 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1362485191) ^ 454161730 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1362485191) ^ 272497038 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1362485191) ^ 123862290 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1362485191) ^ 330 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1444394689 : Nat.Prime 1444394689 := by
  apply lucas_primality 1444394689 (19 : ZMod 1444394689)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 1), (683899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 1), (683899, 1)] : List FactorBlock).map factorBlockValue).prod) = 1444394689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_683899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 1444394689) ^ 722197344 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (19 : ZMod 1444394689) ^ 481464896 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (19 : ZMod 1444394689) ^ 131308608 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (19 : ZMod 1444394689) ^ 2112 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1564867757 : Nat.Prime 1564867757 := by
  apply lucas_primality 1564867757 (2 : ZMod 1564867757)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5399, 1), (72461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5399, 1), (72461, 1)] : List FactorBlock).map factorBlockValue).prod) = 1564867757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5399
      · exact prime_ninetyNineCS_72461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1564867757) ^ 782433878 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564867757) ^ 289844 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564867757) ^ 21596 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1585319111 : Nat.Prime 1585319111 := by
  apply lucas_primality 1585319111 (17 : ZMod 1585319111)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (158531911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (158531911, 1)] : List FactorBlock).map factorBlockValue).prod) = 1585319111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_158531911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 1585319111) ^ 792659555 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 1585319111) ^ 317063822 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 1585319111) ^ 10 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1645922659 : Nat.Prime 1645922659 := by
  apply lucas_primality 1645922659 (2 : ZMod 1645922659)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 1), (2002339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 1), (2002339, 1)] : List FactorBlock).map factorBlockValue).prod) = 1645922659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_137
      · exact prime_ninetyNineCS_2002339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1645922659) ^ 822961329 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1645922659) ^ 548640886 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1645922659) ^ 12014034 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1645922659) ^ 822 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1677288031 : Nat.Prime 1677288031 := by
  apply lucas_primality 1677288031 (6 : ZMod 1677288031)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (5082691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (5082691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1677288031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_5082691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1677288031) ^ 838644015 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1677288031) ^ 559096010 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1677288031) ^ 335457606 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1677288031) ^ 152480730 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1677288031) ^ 330 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1733549749 : Nat.Prime 1733549749 := by
  apply lucas_primality 1733549749 (2 : ZMod 1733549749)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (20637497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (20637497, 1)] : List FactorBlock).map factorBlockValue).prod) = 1733549749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_20637497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1733549749) ^ 866774874 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1733549749) ^ 577849916 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1733549749) ^ 247649964 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1733549749) ^ 84 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1792284803 : Nat.Prime 1792284803 := by
  apply lucas_primality 1792284803 (5 : ZMod 1792284803)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (11638213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (11638213, 1)] : List FactorBlock).map factorBlockValue).prod) = 1792284803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_11638213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1792284803) ^ 896142401 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1792284803) ^ 256040686 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1792284803) ^ 162934982 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1792284803) ^ 154 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2129499557 : Nat.Prime 2129499557 := by
  apply lucas_primality 2129499557 (2 : ZMod 2129499557)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (1321, 1), (21211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (1321, 1), (21211, 1)] : List FactorBlock).map factorBlockValue).prod) = 2129499557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_1321
      · exact prime_ninetyNineCS_21211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2129499557) ^ 1064749778 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2129499557) ^ 112078924 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2129499557) ^ 1612036 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2129499557) ^ 100396 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2425436999 : Nat.Prime 2425436999 := by
  apply lucas_primality 2425436999 (13 : ZMod 2425436999)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1212718499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1212718499, 1)] : List FactorBlock).map factorBlockValue).prod) = 2425436999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_1212718499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 2425436999) ^ 1212718499 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 2425436999) ^ 2 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2640850507 : Nat.Prime 2640850507 := by
  apply lucas_primality 2640850507 (3 : ZMod 2640850507)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (31, 1), (37, 1), (6091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (31, 1), (37, 1), (6091, 1)] : List FactorBlock).map factorBlockValue).prod) = 2640850507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_37
      · exact prime_ninetyNineCS_6091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2640850507) ^ 1320425253 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2640850507) ^ 880283502 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2640850507) ^ 377264358 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2640850507) ^ 85188726 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2640850507) ^ 71374338 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2640850507) ^ 433566 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2732138239 : Nat.Prime 2732138239 := by
  apply lucas_primality 2732138239 (3 : ZMod 2732138239)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (37, 1), (41, 1), (17657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (37, 1), (41, 1), (17657, 1)] : List FactorBlock).map factorBlockValue).prod) = 2732138239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_37
      · exact prime_ninetyNineCS_41
      · exact prime_ninetyNineCS_17657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2732138239) ^ 1366069119 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2732138239) ^ 910712746 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2732138239) ^ 160714014 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2732138239) ^ 73841574 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2732138239) ^ 66637518 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2732138239) ^ 154734 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2840705099 : Nat.Prime 2840705099 := by
  apply lucas_primality 2840705099 (2 : ZMod 2840705099)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (47, 1), (269, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (47, 1), (269, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) = 2840705099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_47
      · exact prime_ninetyNineCS_269
      · exact prime_ninetyNineCS_1459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2840705099) ^ 1420352549 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2840705099) ^ 405815014 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2840705099) ^ 258245918 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2840705099) ^ 60440534 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2840705099) ^ 10560242 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2840705099) ^ 1947022 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2856079549 : Nat.Prime 2856079549 := by
  apply lucas_primality 2856079549 (2 : ZMod 2856079549)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (3777883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (3777883, 1)] : List FactorBlock).map factorBlockValue).prod) = 2856079549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_3777883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2856079549) ^ 1428039774 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2856079549) ^ 952026516 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2856079549) ^ 408011364 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2856079549) ^ 756 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2974567117 : Nat.Prime 2974567117 := by
  apply lucas_primality 2974567117 (2 : ZMod 2974567117)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (13046347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (13046347, 1)] : List FactorBlock).map factorBlockValue).prod) = 2974567117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_13046347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2974567117) ^ 1487283558 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2974567117) ^ 991522372 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2974567117) ^ 156556164 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2974567117) ^ 228 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_3003303007 : Nat.Prime 3003303007 := by
  apply lucas_primality 3003303007 (3 : ZMod 3003303007)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 3), (67, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 3), (67, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) = 3003303007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_67
      · exact prime_ninetyNineCS_1871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3003303007) ^ 1501651503 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3003303007) ^ 1001101002 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3003303007) ^ 273027546 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3003303007) ^ 44825418 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3003303007) ^ 1605186 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_3019760377 : Nat.Prime 3019760377 := by
  apply lucas_primality 3019760377 (10 : ZMod 3019760377)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (499, 1), (252151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (499, 1), (252151, 1)] : List FactorBlock).map factorBlockValue).prod) = 3019760377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_499
      · exact prime_ninetyNineCS_252151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 3019760377) ^ 1509880188 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019760377) ^ 1006586792 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019760377) ^ 6051624 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019760377) ^ 11976 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_3170638223 : Nat.Prime 3170638223 := by
  apply lucas_primality 3170638223 (5 : ZMod 3170638223)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1585319111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1585319111, 1)] : List FactorBlock).map factorBlockValue).prod) = 3170638223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_1585319111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 3170638223) ^ 1585319111 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3170638223) ^ 2 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_3903176143 : Nat.Prime 3903176143 := by
  apply lucas_primality 3903176143 (3 : ZMod 3903176143)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (103, 1), (2105273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (103, 1), (2105273, 1)] : List FactorBlock).map factorBlockValue).prod) = 3903176143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_103
      · exact prime_ninetyNineCS_2105273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3903176143) ^ 1951588071 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3903176143) ^ 1301058714 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3903176143) ^ 37894914 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3903176143) ^ 1854 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_4173434143 : Nat.Prime 4173434143 := by
  apply lucas_primality 4173434143 (7 : ZMod 4173434143)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (5981, 1), (6841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (5981, 1), (6841, 1)] : List FactorBlock).map factorBlockValue).prod) = 4173434143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_5981
      · exact prime_ninetyNineCS_6841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4173434143) ^ 2086717071 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 4173434143) ^ 1391144714 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 4173434143) ^ 245496126 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 4173434143) ^ 697782 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 4173434143) ^ 610062 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_4376800319 : Nat.Prime 4376800319 := by
  apply lucas_primality 4376800319 (11 : ZMod 4376800319)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (8649803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (8649803, 1)] : List FactorBlock).map factorBlockValue).prod) = 4376800319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_23
      · exact prime_ninetyNineCS_8649803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 4376800319) ^ 2188400159 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4376800319) ^ 397890938 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4376800319) ^ 190295666 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4376800319) ^ 506 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_4700769209 : Nat.Prime 4700769209 := by
  apply lucas_primality 4700769209 (3 : ZMod 4700769209)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (137, 1), (41641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (137, 1), (41641, 1)] : List FactorBlock).map factorBlockValue).prod) = 4700769209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_103
      · exact prime_ninetyNineCS_137
      · exact prime_ninetyNineCS_41641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4700769209) ^ 2350384604 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4700769209) ^ 45638536 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4700769209) ^ 34312184 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4700769209) ^ 112888 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_4894699571 : Nat.Prime 4894699571 := by
  apply lucas_primality 4894699571 (6 : ZMod 4894699571)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (489469957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (489469957, 1)] : List FactorBlock).map factorBlockValue).prod) = 4894699571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_489469957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 4894699571) ^ 2447349785 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4894699571) ^ 978939914 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4894699571) ^ 10 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_5572065179 : Nat.Prime 5572065179 := by
  apply lucas_primality 5572065179 (2 : ZMod 5572065179)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (89872019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (89872019, 1)] : List FactorBlock).map factorBlockValue).prod) = 5572065179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_89872019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5572065179) ^ 2786032589 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5572065179) ^ 179744038 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5572065179) ^ 62 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_6150224681 : Nat.Prime 6150224681 := by
  apply lucas_primality 6150224681 (3 : ZMod 6150224681)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (41, 1), (131, 1), (28627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (41, 1), (131, 1), (28627, 1)] : List FactorBlock).map factorBlockValue).prod) = 6150224681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_41
      · exact prime_ninetyNineCS_131
      · exact prime_ninetyNineCS_28627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6150224681) ^ 3075112340 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6150224681) ^ 1230044936 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6150224681) ^ 150005480 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6150224681) ^ 46948280 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6150224681) ^ 214840 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_6423847483 : Nat.Prime 6423847483 := by
  apply lucas_primality 6423847483 (2 : ZMod 6423847483)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (47, 1), (157, 1), (11161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (47, 1), (157, 1), (11161, 1)] : List FactorBlock).map factorBlockValue).prod) = 6423847483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_47
      · exact prime_ninetyNineCS_157
      · exact prime_ninetyNineCS_11161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6423847483) ^ 3211923741 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6423847483) ^ 2141282494 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6423847483) ^ 494142114 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6423847483) ^ 136677606 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6423847483) ^ 40916226 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6423847483) ^ 575562 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_6672763117 : Nat.Prime 6672763117 := by
  apply lucas_primality 6672763117 (5 : ZMod 6672763117)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (313, 1), (691, 1), (857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (313, 1), (691, 1), (857, 1)] : List FactorBlock).map factorBlockValue).prod) = 6672763117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_313
      · exact prime_ninetyNineCS_691
      · exact prime_ninetyNineCS_857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6672763117) ^ 3336381558 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 6672763117) ^ 2224254372 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 6672763117) ^ 21318732 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 6672763117) ^ 9656676 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 6672763117) ^ 7786188 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_8767068397 : Nat.Prime 8767068397 := by
  apply lucas_primality 8767068397 (2 : ZMod 8767068397)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (24623, 1), (29671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (24623, 1), (29671, 1)] : List FactorBlock).map factorBlockValue).prod) = 8767068397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_24623
      · exact prime_ninetyNineCS_29671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8767068397) ^ 4383534198 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 8767068397) ^ 2922356132 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 8767068397) ^ 356052 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 8767068397) ^ 295476 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_10474313243 : Nat.Prime 10474313243 := by
  apply lucas_primality 10474313243 (2 : ZMod 10474313243)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3929, 1), (1332949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3929, 1), (1332949, 1)] : List FactorBlock).map factorBlockValue).prod) = 10474313243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3929
      · exact prime_ninetyNineCS_1332949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10474313243) ^ 5237156621 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10474313243) ^ 2665898 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10474313243) ^ 7858 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_11212036603 : Nat.Prime 11212036603 := by
  apply lucas_primality 11212036603 (3 : ZMod 11212036603)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1531, 1), (93889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1531, 1), (93889, 1)] : List FactorBlock).map factorBlockValue).prod) = 11212036603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_1531
      · exact prime_ninetyNineCS_93889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11212036603) ^ 5606018301 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 11212036603) ^ 3737345534 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 11212036603) ^ 862464354 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 11212036603) ^ 7323342 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 11212036603) ^ 119418 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_11380192669 : Nat.Prime 11380192669 := by
  apply lucas_primality 11380192669 (2 : ZMod 11380192669)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (149, 1), (163199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (149, 1), (163199, 1)] : List FactorBlock).map factorBlockValue).prod) = 11380192669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_149
      · exact prime_ninetyNineCS_163199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11380192669) ^ 5690096334 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380192669) ^ 3793397556 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380192669) ^ 875399436 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380192669) ^ 76377132 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380192669) ^ 69732 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_11736630523 : Nat.Prime 11736630523 := by
  apply lucas_primality 11736630523 (2 : ZMod 11736630523)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (463, 1), (659, 1), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (463, 1), (659, 1), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) = 11736630523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_463
      · exact prime_ninetyNineCS_659
      · exact prime_ninetyNineCS_2137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11736630523) ^ 5868315261 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11736630523) ^ 3912210174 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11736630523) ^ 25349094 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11736630523) ^ 17809758 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 11736630523) ^ 5492106 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_12193857539 : Nat.Prime 12193857539 := by
  apply lucas_primality 12193857539 (2 : ZMod 12193857539)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (2671, 1), (11587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (2671, 1), (11587, 1)] : List FactorBlock).map factorBlockValue).prod) = 12193857539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_197
      · exact prime_ninetyNineCS_2671
      · exact prime_ninetyNineCS_11587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12193857539) ^ 6096928769 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 12193857539) ^ 61897754 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 12193857539) ^ 4565278 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 12193857539) ^ 1052374 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_12855723869 : Nat.Prime 12855723869 := by
  apply lucas_primality 12855723869 (2 : ZMod 12855723869)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (23, 1), (577, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (23, 1), (577, 1), (1433, 1)] : List FactorBlock).map factorBlockValue).prod) = 12855723869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_23
      · exact prime_ninetyNineCS_577
      · exact prime_ninetyNineCS_1433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12855723869) ^ 6427861934 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 12855723869) ^ 988901836 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 12855723869) ^ 558944516 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 12855723869) ^ 22280284 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 12855723869) ^ 8971196 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_14143645819 : Nat.Prime 14143645819 := by
  apply lucas_primality 14143645819 (7 : ZMod 14143645819)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (983, 1), (266449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (983, 1), (266449, 1)] : List FactorBlock).map factorBlockValue).prod) = 14143645819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_983
      · exact prime_ninetyNineCS_266449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 14143645819) ^ 7071822909 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 14143645819) ^ 4714548606 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 14143645819) ^ 14388246 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 14143645819) ^ 53082 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_19660932391 : Nat.Prime 19660932391 := by
  apply lucas_primality 19660932391 (3 : ZMod 19660932391)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (3359, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (3359, 1), (17737, 1)] : List FactorBlock).map factorBlockValue).prod) = 19660932391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_3359
      · exact prime_ninetyNineCS_17737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19660932391) ^ 9830466195 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 19660932391) ^ 6553644130 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 19660932391) ^ 3932186478 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 19660932391) ^ 1787357490 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 19660932391) ^ 5853210 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 19660932391) ^ 1108470 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_21746173307 : Nat.Prime 21746173307 := by
  apply lucas_primality 21746173307 (2 : ZMod 21746173307)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (157, 1), (484303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (157, 1), (484303, 1)] : List FactorBlock).map factorBlockValue).prod) = 21746173307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_157
      · exact prime_ninetyNineCS_484303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21746173307) ^ 10873086653 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 21746173307) ^ 1976924846 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 21746173307) ^ 1672782562 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 21746173307) ^ 138510658 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 21746173307) ^ 44902 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_25150090363 : Nat.Prime 25150090363 := by
  apply lucas_primality 25150090363 (2 : ZMod 25150090363)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (71045453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (71045453, 1)] : List FactorBlock).map factorBlockValue).prod) = 25150090363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_59
      · exact prime_ninetyNineCS_71045453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25150090363) ^ 12575045181 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 25150090363) ^ 8383363454 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 25150090363) ^ 426272718 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 25150090363) ^ 354 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_25758559703 : Nat.Prime 25758559703 := by
  apply lucas_primality 25758559703 (5 : ZMod 25758559703)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (211, 1), (61039241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (211, 1), (61039241, 1)] : List FactorBlock).map factorBlockValue).prod) = 25758559703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_211
      · exact prime_ninetyNineCS_61039241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 25758559703) ^ 12879279851 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 25758559703) ^ 122078482 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 25758559703) ^ 422 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_29356021187 : Nat.Prime 29356021187 := by
  apply lucas_primality 29356021187 (2 : ZMod 29356021187)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (167, 1), (191, 1), (12437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (167, 1), (191, 1), (12437, 1)] : List FactorBlock).map factorBlockValue).prod) = 29356021187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_37
      · exact prime_ninetyNineCS_167
      · exact prime_ninetyNineCS_191
      · exact prime_ninetyNineCS_12437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29356021187) ^ 14678010593 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 29356021187) ^ 793405978 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 29356021187) ^ 175784558 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 29356021187) ^ 153696446 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 29356021187) ^ 2360378 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_29522782703 : Nat.Prime 29522782703 := by
  apply lucas_primality 29522782703 (5 : ZMod 29522782703)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (56993789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (56993789, 1)] : List FactorBlock).map factorBlockValue).prod) = 29522782703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_37
      · exact prime_ninetyNineCS_56993789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29522782703) ^ 14761391351 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 29522782703) ^ 4217540386 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 29522782703) ^ 797913046 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 29522782703) ^ 518 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_30781737289 : Nat.Prime 30781737289 := by
  apply lucas_primality 30781737289 (11 : ZMod 30781737289)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (53, 1), (298759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (53, 1), (298759, 1)] : List FactorBlock).map factorBlockValue).prod) = 30781737289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_53
      · exact prime_ninetyNineCS_298759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 30781737289) ^ 15390868644 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 30781737289) ^ 10260579096 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 30781737289) ^ 580787496 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 30781737289) ^ 103032 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_32108167603 : Nat.Prime 32108167603 := by
  apply lucas_primality 32108167603 (5 : ZMod 32108167603)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (19, 1), (31, 1), (179, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (19, 1), (31, 1), (179, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) = 32108167603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_179
      · exact prime_ninetyNineCS_2417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 32108167603) ^ 16054083801 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 32108167603) ^ 10702722534 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 32108167603) ^ 4586881086 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 32108167603) ^ 1689903558 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 32108167603) ^ 1035747342 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 32108167603) ^ 179375238 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 32108167603) ^ 13284306 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_32294394593 : Nat.Prime 32294394593 := by
  apply lucas_primality 32294394593 (3 : ZMod 32294394593)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (479, 1), (739, 1), (2851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (479, 1), (739, 1), (2851, 1)] : List FactorBlock).map factorBlockValue).prod) = 32294394593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_479
      · exact prime_ninetyNineCS_739
      · exact prime_ninetyNineCS_2851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32294394593) ^ 16147197296 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 32294394593) ^ 67420448 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 32294394593) ^ 43700128 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 32294394593) ^ 11327392 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_32487994883 : Nat.Prime 32487994883 := by
  apply lucas_primality 32487994883 (2 : ZMod 32487994883)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (67, 1), (34635389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (67, 1), (34635389, 1)] : List FactorBlock).map factorBlockValue).prod) = 32487994883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_67
      · exact prime_ninetyNineCS_34635389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32487994883) ^ 16243997441 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 32487994883) ^ 4641142126 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 32487994883) ^ 484895446 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 32487994883) ^ 938 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_36670704067 : Nat.Prime 36670704067 := by
  apply lucas_primality 36670704067 (2 : ZMod 36670704067)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (211, 1), (9655267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (211, 1), (9655267, 1)] : List FactorBlock).map factorBlockValue).prod) = 36670704067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_211
      · exact prime_ninetyNineCS_9655267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36670704067) ^ 18335352033 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36670704067) ^ 12223568022 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36670704067) ^ 173794806 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36670704067) ^ 3798 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_37556826169 : Nat.Prime 37556826169 := by
  apply lucas_primality 37556826169 (19 : ZMod 37556826169)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1564867757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1564867757, 1)] : List FactorBlock).map factorBlockValue).prod) = 37556826169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_1564867757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 37556826169) ^ 18778413084 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (19 : ZMod 37556826169) ^ 12518942056 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (19 : ZMod 37556826169) ^ 24 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_39071364047 : Nat.Prime 39071364047 := by
  apply lucas_primality 39071364047 (5 : ZMod 39071364047)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (47, 1), (2906663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (47, 1), (2906663, 1)] : List FactorBlock).map factorBlockValue).prod) = 39071364047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_47
      · exact prime_ninetyNineCS_2906663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 39071364047) ^ 19535682023 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 39071364047) ^ 3551942186 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 39071364047) ^ 3005489542 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 39071364047) ^ 831305618 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 39071364047) ^ 13442 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_43292299937 : Nat.Prime 43292299937 := by
  apply lucas_primality 43292299937 (3 : ZMod 43292299937)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1213, 1), (1115321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1213, 1), (1115321, 1)] : List FactorBlock).map factorBlockValue).prod) = 43292299937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_1213
      · exact prime_ninetyNineCS_1115321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 43292299937) ^ 21646149968 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 43292299937) ^ 35690272 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 43292299937) ^ 38816 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_44100709189 : Nat.Prime 44100709189 := by
  apply lucas_primality 44100709189 (7 : ZMod 44100709189)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (216179947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (216179947, 1)] : List FactorBlock).map factorBlockValue).prod) = 44100709189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_216179947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 44100709189) ^ 22050354594 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 44100709189) ^ 14700236396 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 44100709189) ^ 2594159364 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 44100709189) ^ 204 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_45532427081 : Nat.Prime 45532427081 := by
  apply lucas_primality 45532427081 (3 : ZMod 45532427081)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (829, 1), (196159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (829, 1), (196159, 1)] : List FactorBlock).map factorBlockValue).prod) = 45532427081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_829
      · exact prime_ninetyNineCS_196159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45532427081) ^ 22766213540 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 45532427081) ^ 9106485416 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 45532427081) ^ 6504632440 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 45532427081) ^ 54924520 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 45532427081) ^ 232120 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_45768280003 : Nat.Prime 45768280003 := by
  apply lucas_primality 45768280003 (2 : ZMod 45768280003)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (3313, 1), (32429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (3313, 1), (32429, 1)] : List FactorBlock).map factorBlockValue).prod) = 45768280003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_71
      · exact prime_ninetyNineCS_3313
      · exact prime_ninetyNineCS_32429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45768280003) ^ 22884140001 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 45768280003) ^ 15256093334 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 45768280003) ^ 644623662 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 45768280003) ^ 13814754 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 45768280003) ^ 1411338 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_45863371943 : Nat.Prime 45863371943 := by
  apply lucas_primality 45863371943 (5 : ZMod 45863371943)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1051, 1), (21818921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1051, 1), (21818921, 1)] : List FactorBlock).map factorBlockValue).prod) = 45863371943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_1051
      · exact prime_ninetyNineCS_21818921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 45863371943) ^ 22931685971 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 45863371943) ^ 43637842 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 45863371943) ^ 2102 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_46964064869 : Nat.Prime 46964064869 := by
  apply lucas_primality 46964064869 (2 : ZMod 46964064869)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1677288031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1677288031, 1)] : List FactorBlock).map factorBlockValue).prod) = 46964064869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_1677288031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46964064869) ^ 23482032434 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 46964064869) ^ 6709152124 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 46964064869) ^ 28 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_49968546521 : Nat.Prime 49968546521 := by
  apply lucas_primality 49968546521 (3 : ZMod 49968546521)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (31253, 1), (39971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (31253, 1), (39971, 1)] : List FactorBlock).map factorBlockValue).prod) = 49968546521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_31253
      · exact prime_ninetyNineCS_39971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 49968546521) ^ 24984273260 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 49968546521) ^ 9993709304 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 49968546521) ^ 1598840 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 49968546521) ^ 1250120 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_50033843627 : Nat.Prime 50033843627 := by
  apply lucas_primality 50033843627 (2 : ZMod 50033843627)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1931, 1), (996571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1931, 1), (996571, 1)] : List FactorBlock).map factorBlockValue).prod) = 50033843627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_1931
      · exact prime_ninetyNineCS_996571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50033843627) ^ 25016921813 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 50033843627) ^ 3848757202 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 50033843627) ^ 25910846 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 50033843627) ^ 50206 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_52933047623 : Nat.Prime 52933047623 := by
  apply lucas_primality 52933047623 (7 : ZMod 52933047623)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (13, 1), (41, 1), (71, 1), (2039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (13, 1), (41, 1), (71, 1), (2039, 1)] : List FactorBlock).map factorBlockValue).prod) = 52933047623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_41
      · exact prime_ninetyNineCS_71
      · exact prime_ninetyNineCS_2039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 52933047623) ^ 26466523811 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 52933047623) ^ 7561863946 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 52933047623) ^ 4071772894 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 52933047623) ^ 1291049942 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 52933047623) ^ 745535882 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 52933047623) ^ 25960298 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_77387997307 : Nat.Prime 77387997307 := by
  apply lucas_primality 77387997307 (3 : ZMod 77387997307)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (439, 1), (29380409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (439, 1), (29380409, 1)] : List FactorBlock).map factorBlockValue).prod) = 77387997307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_439
      · exact prime_ninetyNineCS_29380409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 77387997307) ^ 38693998653 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 77387997307) ^ 25795999102 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 77387997307) ^ 176282454 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 77387997307) ^ 2634 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_87962227547 : Nat.Prime 87962227547 := by
  apply lucas_primality 87962227547 (2 : ZMod 87962227547)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1361, 1), (32315293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1361, 1), (32315293, 1)] : List FactorBlock).map factorBlockValue).prod) = 87962227547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_1361
      · exact prime_ninetyNineCS_32315293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 87962227547) ^ 43981113773 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 87962227547) ^ 64630586 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 87962227547) ^ 2722 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_91064854163 : Nat.Prime 91064854163 := by
  apply lucas_primality 91064854163 (2 : ZMod 91064854163)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (45532427081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (45532427081, 1)] : List FactorBlock).map factorBlockValue).prod) = 91064854163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_45532427081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 91064854163) ^ 45532427081 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 91064854163) ^ 2 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_111984858901 : Nat.Prime 111984858901 := by
  apply lucas_primality 111984858901 (2 : ZMod 111984858901)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (5563, 1), (22367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (5563, 1), (22367, 1)] : List FactorBlock).map factorBlockValue).prod) = 111984858901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_5563
      · exact prime_ninetyNineCS_22367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 111984858901) ^ 55992429450 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 111984858901) ^ 37328286300 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 111984858901) ^ 22396971780 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 111984858901) ^ 20130300 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 111984858901) ^ 5006700 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_140025802019 : Nat.Prime 140025802019 := by
  apply lucas_primality 140025802019 (2 : ZMod 140025802019)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (679736903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (679736903, 1)] : List FactorBlock).map factorBlockValue).prod) = 140025802019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_103
      · exact prime_ninetyNineCS_679736903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 140025802019) ^ 70012901009 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 140025802019) ^ 1359473806 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 140025802019) ^ 206 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_212385819473 : Nat.Prime 212385819473 := by
  apply lucas_primality 212385819473 (3 : ZMod 212385819473)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (43, 1), (137, 1), (313, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (43, 1), (137, 1), (313, 2)] : List FactorBlock).map factorBlockValue).prod) = 212385819473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_23
      · exact prime_ninetyNineCS_43
      · exact prime_ninetyNineCS_137
      · exact prime_ninetyNineCS_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 212385819473) ^ 106192909736 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 212385819473) ^ 9234166064 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 212385819473) ^ 4939205104 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 212385819473) ^ 1550261456 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 212385819473) ^ 678548944 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_231403029643 : Nat.Prime 231403029643 := by
  apply lucas_primality 231403029643 (2 : ZMod 231403029643)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (12855723869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (12855723869, 1)] : List FactorBlock).map factorBlockValue).prod) = 231403029643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_12855723869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 231403029643) ^ 115701514821 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 231403029643) ^ 77134343214 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 231403029643) ^ 18 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_335178023777 : Nat.Prime 335178023777 := by
  apply lucas_primality 335178023777 (3 : ZMod 335178023777)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (10474313243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (10474313243, 1)] : List FactorBlock).map factorBlockValue).prod) = 335178023777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_10474313243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 335178023777) ^ 167589011888 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 335178023777) ^ 32 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_346338399497 : Nat.Prime 346338399497 := by
  apply lucas_primality 346338399497 (3 : ZMod 346338399497)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43292299937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43292299937, 1)] : List FactorBlock).map factorBlockValue).prod) = 346338399497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_43292299937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 346338399497) ^ 173169199748 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 346338399497) ^ 8 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_503091418393 : Nat.Prime 503091418393 := by
  apply lucas_primality 503091418393 (5 : ZMod 503091418393)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (31, 1), (75133127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (31, 1), (75133127, 1)] : List FactorBlock).map factorBlockValue).prod) = 503091418393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_75133127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 503091418393) ^ 251545709196 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 503091418393) ^ 167697139464 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 503091418393) ^ 16228755432 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 503091418393) ^ 6696 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_516286178983 : Nat.Prime 516286178983 := by
  apply lucas_primality 516286178983 (5 : ZMod 516286178983)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (23017, 1), (178021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (23017, 1), (178021, 1)] : List FactorBlock).map factorBlockValue).prod) = 516286178983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_23017
      · exact prime_ninetyNineCS_178021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 516286178983) ^ 258143089491 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 516286178983) ^ 172095392994 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 516286178983) ^ 73755168426 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 516286178983) ^ 22430646 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 516286178983) ^ 2900142 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_611436722293 : Nat.Prime 611436722293 := by
  apply lucas_primality 611436722293 (2 : ZMod 611436722293)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 2), (1291, 1), (108727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 2), (1291, 1), (108727, 1)] : List FactorBlock).map factorBlockValue).prod) = 611436722293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_1291
      · exact prime_ninetyNineCS_108727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 611436722293) ^ 305718361146 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 611436722293) ^ 203812240764 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 611436722293) ^ 55585156572 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 611436722293) ^ 473614812 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 611436722293) ^ 5623596 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_770926150277 : Nat.Prime 770926150277 := by
  apply lucas_primality 770926150277 (2 : ZMod 770926150277)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (4700769209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (4700769209, 1)] : List FactorBlock).map factorBlockValue).prod) = 770926150277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_41
      · exact prime_ninetyNineCS_4700769209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 770926150277) ^ 385463075138 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 770926150277) ^ 18803076836 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 770926150277) ^ 164 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_803338385459 : Nat.Prime 803338385459 := by
  apply lucas_primality 803338385459 (2 : ZMod 803338385459)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (151, 1), (8171, 1), (46507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (151, 1), (8171, 1), (46507, 1)] : List FactorBlock).map factorBlockValue).prod) = 803338385459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_151
      · exact prime_ninetyNineCS_8171
      · exact prime_ninetyNineCS_46507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 803338385459) ^ 401669192729 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 803338385459) ^ 114762626494 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 803338385459) ^ 5320121758 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 803338385459) ^ 98315798 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 803338385459) ^ 17273494 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_925612118573 : Nat.Prime 925612118573 := by
  apply lucas_primality 925612118573 (2 : ZMod 925612118573)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (231403029643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (231403029643, 1)] : List FactorBlock).map factorBlockValue).prod) = 925612118573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_231403029643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 925612118573) ^ 462806059286 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 925612118573) ^ 4 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_952577592199 : Nat.Prime 952577592199 := by
  apply lucas_primality 952577592199 (6 : ZMod 952577592199)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (84631, 1), (1875943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (84631, 1), (1875943, 1)] : List FactorBlock).map factorBlockValue).prod) = 952577592199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_84631
      · exact prime_ninetyNineCS_1875943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 952577592199) ^ 476288796099 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 952577592199) ^ 317525864066 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 952577592199) ^ 11255658 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 952577592199) ^ 507786 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_953317253093 : Nat.Prime 953317253093 := by
  apply lucas_primality 953317253093 (2 : ZMod 953317253093)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (19, 1), (151, 1), (4886501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (19, 1), (151, 1), (4886501, 1)] : List FactorBlock).map factorBlockValue).prod) = 953317253093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_151
      · exact prime_ninetyNineCS_4886501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 953317253093) ^ 476658626546 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 953317253093) ^ 56077485476 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 953317253093) ^ 50174592268 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 953317253093) ^ 6313359292 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 953317253093) ^ 195092 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1479409203533 : Nat.Prime 1479409203533 := by
  apply lucas_primality 1479409203533 (3 : ZMod 1479409203533)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 2), (23, 1), (4280153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 2), (23, 1), (4280153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1479409203533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_23
      · exact prime_ninetyNineCS_4280153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1479409203533) ^ 739704601766 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1479409203533) ^ 113800707964 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1479409203533) ^ 87024070796 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1479409203533) ^ 64322139284 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1479409203533) ^ 345644 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1525502146351 : Nat.Prime 1525502146351 := by
  apply lucas_primality 1525502146351 (3 : ZMod 1525502146351)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (13, 1), (19, 1), (103, 1), (57107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (13, 1), (19, 1), (103, 1), (57107, 1)] : List FactorBlock).map factorBlockValue).prod) = 1525502146351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_103
      · exact prime_ninetyNineCS_57107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1525502146351) ^ 762751073175 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1525502146351) ^ 508500715450 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1525502146351) ^ 305100429270 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1525502146351) ^ 217928878050 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1525502146351) ^ 117346318950 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1525502146351) ^ 80289586650 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1525502146351) ^ 14810700450 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1525502146351) ^ 26713050 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1544657291101 : Nat.Prime 1544657291101 := by
  apply lucas_primality 1544657291101 (10 : ZMod 1544657291101)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 2), (7, 1), (11, 1), (89, 1), (27827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 2), (7, 1), (11, 1), (89, 1), (27827, 1)] : List FactorBlock).map factorBlockValue).prod) = 1544657291101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_89
      · exact prime_ninetyNineCS_27827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1544657291101) ^ 772328645550 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1544657291101) ^ 514885763700 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1544657291101) ^ 308931458220 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1544657291101) ^ 220665327300 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1544657291101) ^ 140423390100 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1544657291101) ^ 17355699900 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 1544657291101) ^ 55509300 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1597030701587 : Nat.Prime 1597030701587 := by
  apply lucas_primality 1597030701587 (2 : ZMod 1597030701587)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (25758559703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (25758559703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1597030701587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_25758559703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1597030701587) ^ 798515350793 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597030701587) ^ 51517119406 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597030701587) ^ 62 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1829974788463 : Nat.Prime 1829974788463 := by
  apply lucas_primality 1829974788463 (3 : ZMod 1829974788463)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (3019760377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (3019760377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1829974788463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_101
      · exact prime_ninetyNineCS_3019760377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1829974788463) ^ 914987394231 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1829974788463) ^ 609991596154 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1829974788463) ^ 18118562262 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1829974788463) ^ 606 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1873059985943 : Nat.Prime 1873059985943 := by
  apply lucas_primality 1873059985943 (5 : ZMod 1873059985943)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (569, 1), (1645922659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (569, 1), (1645922659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1873059985943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_569
      · exact prime_ninetyNineCS_1645922659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1873059985943) ^ 936529992971 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1873059985943) ^ 3291845318 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1873059985943) ^ 1138 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1964043666679 : Nat.Prime 1964043666679 := by
  apply lucas_primality 1964043666679 (6 : ZMod 1964043666679)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (60443, 1), (5415691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (60443, 1), (5415691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1964043666679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_60443
      · exact prime_ninetyNineCS_5415691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1964043666679) ^ 982021833339 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1964043666679) ^ 654681222226 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1964043666679) ^ 32494146 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1964043666679) ^ 362658 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2572873123057 : Nat.Prime 2572873123057 := by
  apply lucas_primality 2572873123057 (5 : ZMod 2572873123057)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (5413, 1), (341461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (5413, 1), (341461, 1)] : List FactorBlock).map factorBlockValue).prod) = 2572873123057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_29
      · exact prime_ninetyNineCS_5413
      · exact prime_ninetyNineCS_341461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2572873123057) ^ 1286436561528 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2572873123057) ^ 857624374352 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2572873123057) ^ 88719762864 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2572873123057) ^ 475313712 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2572873123057) ^ 7534896 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2810516374927 : Nat.Prime 2810516374927 := by
  apply lucas_primality 2810516374927 (5 : ZMod 2810516374927)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (31, 1), (387443669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (31, 1), (387443669, 1)] : List FactorBlock).map factorBlockValue).prod) = 2810516374927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_387443669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2810516374927) ^ 1405258187463 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2810516374927) ^ 936838791642 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2810516374927) ^ 216193567302 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2810516374927) ^ 90661818546 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2810516374927) ^ 7254 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_3263568267301 : Nat.Prime 3263568267301 := by
  apply lucas_primality 3263568267301 (2 : ZMod 3263568267301)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 1), (277, 2), (12889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 1), (277, 2), (12889, 1)] : List FactorBlock).map factorBlockValue).prod) = 3263568267301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_277
      · exact prime_ninetyNineCS_12889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3263568267301) ^ 1631784133650 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3263568267301) ^ 1087856089100 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3263568267301) ^ 652713653460 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3263568267301) ^ 296688024300 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3263568267301) ^ 11781834900 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3263568267301) ^ 253205700 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_3746119971887 : Nat.Prime 3746119971887 := by
  apply lucas_primality 3746119971887 (5 : ZMod 3746119971887)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1873059985943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1873059985943, 1)] : List FactorBlock).map factorBlockValue).prod) = 3746119971887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_1873059985943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 3746119971887) ^ 1873059985943 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3746119971887) ^ 2 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_4200244569419 : Nat.Prime 4200244569419 := by
  apply lucas_primality 4200244569419 (2 : ZMod 4200244569419)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (67, 1), (764514847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (67, 1), (764514847, 1)] : List FactorBlock).map factorBlockValue).prod) = 4200244569419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_41
      · exact prime_ninetyNineCS_67
      · exact prime_ninetyNineCS_764514847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4200244569419) ^ 2100122284709 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4200244569419) ^ 102444989498 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4200244569419) ^ 62690217454 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4200244569419) ^ 5494 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_4552086860819 : Nat.Prime 4552086860819 := by
  apply lucas_primality 4552086860819 (6 : ZMod 4552086860819)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (11212036603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (11212036603, 1)] : List FactorBlock).map factorBlockValue).prod) = 4552086860819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_29
      · exact prime_ninetyNineCS_11212036603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4552086860819) ^ 2276043430409 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4552086860819) ^ 650298122974 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4552086860819) ^ 156968512442 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 4552086860819) ^ 406 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_5343813810781 : Nat.Prime 5343813810781 := by
  apply lucas_primality 5343813810781 (2 : ZMod 5343813810781)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (149, 1), (193, 1), (1291, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (149, 1), (193, 1), (1291, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) = 5343813810781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_149
      · exact prime_ninetyNineCS_193
      · exact prime_ninetyNineCS_1291
      · exact prime_ninetyNineCS_2399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5343813810781) ^ 2671906905390 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5343813810781) ^ 1781271270260 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5343813810781) ^ 1068762762156 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5343813810781) ^ 35864522220 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5343813810781) ^ 27688154460 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5343813810781) ^ 4139282580 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 5343813810781) ^ 2227517220 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_6053965096477 : Nat.Prime 6053965096477 := by
  apply lucas_primality 6053965096477 (5 : ZMod 6053965096477)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (45863371943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (45863371943, 1)] : List FactorBlock).map factorBlockValue).prod) = 6053965096477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_45863371943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6053965096477) ^ 3026982548238 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 6053965096477) ^ 2017988365492 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 6053965096477) ^ 550360463316 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 6053965096477) ^ 132 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_6161135288837 : Nat.Prime 6161135288837 := by
  apply lucas_primality 6161135288837 (2 : ZMod 6161135288837)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (140025802019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (140025802019, 1)] : List FactorBlock).map factorBlockValue).prod) = 6161135288837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_140025802019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6161135288837) ^ 3080567644418 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6161135288837) ^ 560103208076 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6161135288837) ^ 44 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_6595184164489 : Nat.Prime 6595184164489 := by
  apply lucas_primality 6595184164489 (11 : ZMod 6595184164489)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (53441, 1), (5142107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (53441, 1), (5142107, 1)] : List FactorBlock).map factorBlockValue).prod) = 6595184164489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_53441
      · exact prime_ninetyNineCS_5142107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 6595184164489) ^ 3297592082244 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 6595184164489) ^ 2198394721496 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 6595184164489) ^ 123410568 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 6595184164489) ^ 1282584 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_6615387246551 : Nat.Prime 6615387246551 := by
  apply lucas_primality 6615387246551 (13 : ZMod 6615387246551)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (137, 1), (271, 1), (3563653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (137, 1), (271, 1), (3563653, 1)] : List FactorBlock).map factorBlockValue).prod) = 6615387246551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_137
      · exact prime_ninetyNineCS_271
      · exact prime_ninetyNineCS_3563653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 6615387246551) ^ 3307693623275 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 6615387246551) ^ 1323077449310 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 6615387246551) ^ 48287498150 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 6615387246551) ^ 24411023050 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 6615387246551) ^ 1856350 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_10335976687219 : Nat.Prime 10335976687219 := by
  apply lucas_primality 10335976687219 (7 : ZMod 10335976687219)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (503, 1), (37634911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (503, 1), (37634911, 1)] : List FactorBlock).map factorBlockValue).prod) = 10335976687219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_503
      · exact prime_ninetyNineCS_37634911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10335976687219) ^ 5167988343609 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 10335976687219) ^ 3445325562406 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 10335976687219) ^ 1476568098174 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 10335976687219) ^ 795075129786 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 10335976687219) ^ 20548661406 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 10335976687219) ^ 274638 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_10439585944937 : Nat.Prime 10439585944937 := by
  apply lucas_primality 10439585944937 (3 : ZMod 10439585944937)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4909, 1), (265827713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4909, 1), (265827713, 1)] : List FactorBlock).map factorBlockValue).prod) = 10439585944937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_4909
      · exact prime_ninetyNineCS_265827713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10439585944937) ^ 5219792972468 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 10439585944937) ^ 2126621704 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 10439585944937) ^ 39272 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_11078468944849 : Nat.Prime 11078468944849 := by
  apply lucas_primality 11078468944849 (7 : ZMod 11078468944849)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (29, 1), (79, 1), (83, 1), (157, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (29, 1), (79, 1), (83, 1), (157, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) = 11078468944849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_29
      · exact prime_ninetyNineCS_79
      · exact prime_ninetyNineCS_83
      · exact prime_ninetyNineCS_157
      · exact prime_ninetyNineCS_859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11078468944849) ^ 5539234472424 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 11078468944849) ^ 3692822981616 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 11078468944849) ^ 382016170512 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 11078468944849) ^ 140233784112 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 11078468944849) ^ 133475529456 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 11078468944849) ^ 70563496464 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 11078468944849) ^ 12896937072 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_11770692816901 : Nat.Prime 11770692816901 := by
  apply lucas_primality 11770692816901 (13 : ZMod 11770692816901)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (47, 1), (1871, 1), (446179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (47, 1), (1871, 1), (446179, 1)] : List FactorBlock).map factorBlockValue).prod) = 11770692816901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_47
      · exact prime_ninetyNineCS_1871
      · exact prime_ninetyNineCS_446179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 11770692816901) ^ 5885346408450 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 11770692816901) ^ 3923564272300 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 11770692816901) ^ 2354138563380 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 11770692816901) ^ 250440272700 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 11770692816901) ^ 6291123900 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 11770692816901) ^ 26381100 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_12906654960847 : Nat.Prime 12906654960847 := by
  apply lucas_primality 12906654960847 (7 : ZMod 12906654960847)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (45768280003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (45768280003, 1)] : List FactorBlock).map factorBlockValue).prod) = 12906654960847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_47
      · exact prime_ninetyNineCS_45768280003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 12906654960847) ^ 6453327480423 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 12906654960847) ^ 4302218320282 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 12906654960847) ^ 274609680018 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 12906654960847) ^ 282 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_13230774493103 : Nat.Prime 13230774493103 := by
  apply lucas_primality 13230774493103 (5 : ZMod 13230774493103)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6615387246551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6615387246551, 1)] : List FactorBlock).map factorBlockValue).prod) = 13230774493103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_6615387246551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 13230774493103) ^ 6615387246551 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 13230774493103) ^ 2 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_15258909473999 : Nat.Prime 15258909473999 := by
  apply lucas_primality 15258909473999 (7 : ZMod 15258909473999)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (563, 1), (17327, 1), (25229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (563, 1), (17327, 1), (25229, 1)] : List FactorBlock).map factorBlockValue).prod) = 15258909473999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_563
      · exact prime_ninetyNineCS_17327
      · exact prime_ninetyNineCS_25229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15258909473999) ^ 7629454736999 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 15258909473999) ^ 492222886258 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 15258909473999) ^ 27102858746 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 15258909473999) ^ 880643474 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 15258909473999) ^ 604816262 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_29721304985747 : Nat.Prime 29721304985747 := by
  apply lucas_primality 29721304985747 (2 : ZMod 29721304985747)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (557, 1), (2425436999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (557, 1), (2425436999, 1)] : List FactorBlock).map factorBlockValue).prod) = 29721304985747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_557
      · exact prime_ninetyNineCS_2425436999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 29721304985747) ^ 14860652492873 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 29721304985747) ^ 2701936816886 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 29721304985747) ^ 53359613978 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 29721304985747) ^ 12254 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_31470894077911 : Nat.Prime 31470894077911 := by
  apply lucas_primality 31470894077911 (7 : ZMod 31470894077911)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1039, 1), (144236189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1039, 1), (144236189, 1)] : List FactorBlock).map factorBlockValue).prod) = 31470894077911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_1039
      · exact prime_ninetyNineCS_144236189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 31470894077911) ^ 15735447038955 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 31470894077911) ^ 10490298025970 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 31470894077911) ^ 6294178815582 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 31470894077911) ^ 4495842011130 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 31470894077911) ^ 30289599690 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 31470894077911) ^ 218190 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_36496536670081 : Nat.Prime 36496536670081 := by
  apply lucas_primality 36496536670081 (13 : ZMod 36496536670081)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 1), (17, 1), (1129, 1), (330131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 1), (17, 1), (1129, 1), (330131, 1)] : List FactorBlock).map factorBlockValue).prod) = 36496536670081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_1129
      · exact prime_ninetyNineCS_330131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 36496536670081) ^ 18248268335040 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 36496536670081) ^ 12165512223360 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 36496536670081) ^ 7299307334016 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 36496536670081) ^ 2146855098240 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 36496536670081) ^ 32326427520 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 36496536670081) ^ 110551680 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_44455765394431 : Nat.Prime 44455765394431 := by
  apply lucas_primality 44455765394431 (15 : ZMod 44455765394431)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (53, 1), (3929, 1), (182467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (53, 1), (3929, 1), (182467, 1)] : List FactorBlock).map factorBlockValue).prod) = 44455765394431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_53
      · exact prime_ninetyNineCS_3929
      · exact prime_ninetyNineCS_182467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 44455765394431) ^ 22227882697215 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (15 : ZMod 44455765394431) ^ 14818588464810 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (15 : ZMod 44455765394431) ^ 8891153078886 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (15 : ZMod 44455765394431) ^ 3419674261110 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (15 : ZMod 44455765394431) ^ 838788026310 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (15 : ZMod 44455765394431) ^ 11314778670 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (15 : ZMod 44455765394431) ^ 243637290 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_56529111096421 : Nat.Prime 56529111096421 := by
  apply lucas_primality 56529111096421 (2 : ZMod 56529111096421)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (32487994883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (32487994883, 1)] : List FactorBlock).map factorBlockValue).prod) = 56529111096421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_29
      · exact prime_ninetyNineCS_32487994883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56529111096421) ^ 28264555548210 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 56529111096421) ^ 18843037032140 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 56529111096421) ^ 11305822219284 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 56529111096421) ^ 1949279692980 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 56529111096421) ^ 1740 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_56615609891777 : Nat.Prime 56615609891777 := by
  apply lucas_primality 56615609891777 (3 : ZMod 56615609891777)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (139, 1), (489551137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (139, 1), (489551137, 1)] : List FactorBlock).map factorBlockValue).prod) = 56615609891777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_139
      · exact prime_ninetyNineCS_489551137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56615609891777) ^ 28307804945888 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 56615609891777) ^ 4355046914752 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 56615609891777) ^ 407306545984 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 56615609891777) ^ 115648 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_71345710296383 : Nat.Prime 71345710296383 := by
  apply lucas_primality 71345710296383 (5 : ZMod 71345710296383)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (346338399497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (346338399497, 1)] : List FactorBlock).map factorBlockValue).prod) = 71345710296383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_103
      · exact prime_ninetyNineCS_346338399497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 71345710296383) ^ 35672855148191 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 71345710296383) ^ 692676798994 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 71345710296383) ^ 206 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_73695808461227 : Nat.Prime 73695808461227 := by
  apply lucas_primality 73695808461227 (2 : ZMod 73695808461227)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (163, 1), (32294394593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (163, 1), (32294394593, 1)] : List FactorBlock).map factorBlockValue).prod) = 73695808461227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_163
      · exact prime_ninetyNineCS_32294394593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73695808461227) ^ 36847904230613 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 73695808461227) ^ 10527972637318 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 73695808461227) ^ 452121524302 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 73695808461227) ^ 2282 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_85803871067093 : Nat.Prime 85803871067093 := by
  apply lucas_primality 85803871067093 (2 : ZMod 85803871067093)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (212385819473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (212385819473, 1)] : List FactorBlock).map factorBlockValue).prod) = 85803871067093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_101
      · exact prime_ninetyNineCS_212385819473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 85803871067093) ^ 42901935533546 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 85803871067093) ^ 849543277892 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 85803871067093) ^ 404 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_99019588599233 : Nat.Prime 99019588599233 := by
  apply lucas_primality 99019588599233 (5 : ZMod 99019588599233)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (181, 1), (233, 1), (349, 1), (15017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (181, 1), (233, 1), (349, 1), (15017, 1)] : List FactorBlock).map factorBlockValue).prod) = 99019588599233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_181
      · exact prime_ninetyNineCS_233
      · exact prime_ninetyNineCS_349
      · exact prime_ninetyNineCS_15017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 99019588599233) ^ 49509794299616 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 99019588599233) ^ 14145655514176 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 99019588599233) ^ 547069550272 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 99019588599233) ^ 424976775104 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 99019588599233) ^ 283723749568 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 99019588599233) ^ 6593832896 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_168294453805991 : Nat.Prime 168294453805991 := by
  apply lucas_primality 168294453805991 (7 : ZMod 168294453805991)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (25693, 1), (655020643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (25693, 1), (655020643, 1)] : List FactorBlock).map factorBlockValue).prod) = 168294453805991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_25693
      · exact prime_ninetyNineCS_655020643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 168294453805991) ^ 84147226902995 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 168294453805991) ^ 33658890761198 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 168294453805991) ^ 6550206430 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 168294453805991) ^ 256930 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_236532891212363 : Nat.Prime 236532891212363 := by
  apply lucas_primality 236532891212363 (2 : ZMod 236532891212363)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (67, 1), (37556826169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (67, 1), (37556826169, 1)] : List FactorBlock).map factorBlockValue).prod) = 236532891212363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_47
      · exact prime_ninetyNineCS_67
      · exact prime_ninetyNineCS_37556826169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 236532891212363) ^ 118266445606181 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 236532891212363) ^ 5032614706646 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 236532891212363) ^ 3530341659886 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 236532891212363) ^ 6298 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_247862485804181 : Nat.Prime 247862485804181 := by
  apply lucas_primality 247862485804181 (2 : ZMod 247862485804181)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (953317253093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (953317253093, 1)] : List FactorBlock).map factorBlockValue).prod) = 247862485804181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_953317253093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 247862485804181) ^ 123931242902090 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 247862485804181) ^ 49572497160836 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 247862485804181) ^ 19066345061860 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 247862485804181) ^ 260 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_323462361986977 : Nat.Prime 323462361986977 := by
  apply lucas_primality 323462361986977 (5 : ZMod 323462361986977)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (37, 1), (91064854163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (37, 1), (91064854163, 1)] : List FactorBlock).map factorBlockValue).prod) = 323462361986977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_37
      · exact prime_ninetyNineCS_91064854163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 323462361986977) ^ 161731180993488 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 323462361986977) ^ 107820787328992 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 323462361986977) ^ 8742225999648 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 323462361986977) ^ 3552 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_420798021226241 : Nat.Prime 420798021226241 := by
  apply lucas_primality 420798021226241 (3 : ZMod 420798021226241)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (7, 1), (46964064869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (7, 1), (46964064869, 1)] : List FactorBlock).map factorBlockValue).prod) = 420798021226241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_46964064869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 420798021226241) ^ 210399010613120 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 420798021226241) ^ 84159604245248 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 420798021226241) ^ 60114003032320 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 420798021226241) ^ 8960 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_423554658244573 : Nat.Prime 423554658244573 := by
  apply lucas_primality 423554658244573 (2 : ZMod 423554658244573)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (823, 1), (70003, 1), (612649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (823, 1), (70003, 1), (612649, 1)] : List FactorBlock).map factorBlockValue).prod) = 423554658244573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_823
      · exact prime_ninetyNineCS_70003
      · exact prime_ninetyNineCS_612649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 423554658244573) ^ 211777329122286 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 423554658244573) ^ 141184886081524 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 423554658244573) ^ 514647215364 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 423554658244573) ^ 6050521524 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 423554658244573) ^ 691349628 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_426006518330923 : Nat.Prime 426006518330923 := by
  apply lucas_primality 426006518330923 (22 : ZMod 426006518330923)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (503, 1), (3003303007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (503, 1), (3003303007, 1)] : List FactorBlock).map factorBlockValue).prod) = 426006518330923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_47
      · exact prime_ninetyNineCS_503
      · exact prime_ninetyNineCS_3003303007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 426006518330923) ^ 213003259165461 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (22 : ZMod 426006518330923) ^ 142002172776974 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (22 : ZMod 426006518330923) ^ 9063968475126 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (22 : ZMod 426006518330923) ^ 846931447974 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (22 : ZMod 426006518330923) ^ 141846 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_518937902133367 : Nat.Prime 518937902133367 := by
  apply lucas_primality 518937902133367 (3 : ZMod 518937902133367)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (4552086860819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (4552086860819, 1)] : List FactorBlock).map factorBlockValue).prod) = 518937902133367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_4552086860819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 518937902133367) ^ 259468951066683 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 518937902133367) ^ 172979300711122 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 518937902133367) ^ 27312521164914 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 518937902133367) ^ 114 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_583128628247651 : Nat.Prime 583128628247651 := by
  apply lucas_primality 583128628247651 (2 : ZMod 583128628247651)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (127, 1), (15101, 1), (6081139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (127, 1), (15101, 1), (6081139, 1)] : List FactorBlock).map factorBlockValue).prod) = 583128628247651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_127
      · exact prime_ninetyNineCS_15101
      · exact prime_ninetyNineCS_6081139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 583128628247651) ^ 291564314123825 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 583128628247651) ^ 116625725649530 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 583128628247651) ^ 4591564001950 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 583128628247651) ^ 38615232650 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 583128628247651) ^ 95891350 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_682509969998383 : Nat.Prime 682509969998383 := by
  apply lucas_primality 682509969998383 (3 : ZMod 682509969998383)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1218571, 1), (93348407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1218571, 1), (93348407, 1)] : List FactorBlock).map factorBlockValue).prod) = 682509969998383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_1218571
      · exact prime_ninetyNineCS_93348407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 682509969998383) ^ 341254984999191 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 682509969998383) ^ 227503323332794 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 682509969998383) ^ 560090442 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 682509969998383) ^ 7311426 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1961606129059303 : Nat.Prime 1961606129059303 := by
  apply lucas_primality 1961606129059303 (5 : ZMod 1961606129059303)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (29721304985747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (29721304985747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1961606129059303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_29721304985747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1961606129059303) ^ 980803064529651 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1961606129059303) ^ 653868709686434 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1961606129059303) ^ 178327829914482 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1961606129059303) ^ 66 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2296291140731683 : Nat.Prime 2296291140731683 := by
  apply lucas_primality 2296291140731683 (2 : ZMod 2296291140731683)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (79, 1), (17971, 1), (89857661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (79, 1), (17971, 1), (89857661, 1)] : List FactorBlock).map factorBlockValue).prod) = 2296291140731683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_79
      · exact prime_ninetyNineCS_17971
      · exact prime_ninetyNineCS_89857661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2296291140731683) ^ 1148145570365841 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296291140731683) ^ 765430380243894 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296291140731683) ^ 29066976464958 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296291140731683) ^ 127777593942 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2296291140731683) ^ 25554762 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_3153387662666257 : Nat.Prime 3153387662666257 := by
  apply lucas_primality 3153387662666257 (5 : ZMod 3153387662666257)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (43, 1), (173, 1), (719, 1), (534029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (43, 1), (173, 1), (719, 1), (534029, 1)] : List FactorBlock).map factorBlockValue).prod) = 3153387662666257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_23
      · exact prime_ninetyNineCS_43
      · exact prime_ninetyNineCS_173
      · exact prime_ninetyNineCS_719
      · exact prime_ninetyNineCS_534029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3153387662666257) ^ 1576693831333128 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3153387662666257) ^ 1051129220888752 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3153387662666257) ^ 137103811420272 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3153387662666257) ^ 73334596806192 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3153387662666257) ^ 18227674350672 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3153387662666257) ^ 4385796471024 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 3153387662666257) ^ 5904899664 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_3798879437689613 : Nat.Prime 3798879437689613 := by
  apply lucas_primality 3798879437689613 (2 : ZMod 3798879437689613)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (997, 1), (952577592199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (997, 1), (952577592199, 1)] : List FactorBlock).map factorBlockValue).prod) = 3798879437689613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_997
      · exact prime_ninetyNineCS_952577592199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3798879437689613) ^ 1899439718844806 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3798879437689613) ^ 3810310368796 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3798879437689613) ^ 3988 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_4612127290978073 : Nat.Prime 4612127290978073 := by
  apply lucas_primality 4612127290978073 (3 : ZMod 4612127290978073)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (93739, 1), (6150224681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (93739, 1), (6150224681, 1)] : List FactorBlock).map factorBlockValue).prod) = 4612127290978073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_93739
      · exact prime_ninetyNineCS_6150224681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4612127290978073) ^ 2306063645489036 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4612127290978073) ^ 49201797448 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4612127290978073) ^ 749912 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_4817542840450693 : Nat.Prime 4817542840450693 := by
  apply lucas_primality 4817542840450693 (2 : ZMod 4817542840450693)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (36496536670081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (36496536670081, 1)] : List FactorBlock).map factorBlockValue).prod) = 4817542840450693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_36496536670081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4817542840450693) ^ 2408771420225346 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4817542840450693) ^ 1605847613483564 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4817542840450693) ^ 437958440040972 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4817542840450693) ^ 132 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_6267656526478681 : Nat.Prime 6267656526478681 := by
  apply lucas_primality 6267656526478681 (7 : ZMod 6267656526478681)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (83, 1), (355573, 1), (1769771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (83, 1), (355573, 1), (1769771, 1)] : List FactorBlock).map factorBlockValue).prod) = 6267656526478681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_83
      · exact prime_ninetyNineCS_355573
      · exact prime_ninetyNineCS_1769771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6267656526478681) ^ 3133828263239340 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 6267656526478681) ^ 2089218842159560 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 6267656526478681) ^ 1253531305295736 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 6267656526478681) ^ 75513934053960 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 6267656526478681) ^ 17626919160 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 6267656526478681) ^ 3541507080 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_6524917297242259 : Nat.Prime 6524917297242259 := by
  apply lucas_primality 6524917297242259 (3 : ZMod 6524917297242259)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (73, 1), (29611, 1), (7508843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (73, 1), (29611, 1), (7508843, 1)] : List FactorBlock).map factorBlockValue).prod) = 6524917297242259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_67
      · exact prime_ninetyNineCS_73
      · exact prime_ninetyNineCS_29611
      · exact prime_ninetyNineCS_7508843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6524917297242259) ^ 3262458648621129 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6524917297242259) ^ 2174972432414086 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6524917297242259) ^ 97386825331974 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6524917297242259) ^ 89382428729346 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6524917297242259) ^ 220354506678 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6524917297242259) ^ 868964406 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_7926051476989099 : Nat.Prime 7926051476989099 := by
  apply lucas_primality 7926051476989099 (3 : ZMod 7926051476989099)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (27737, 1), (299536001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (27737, 1), (299536001, 1)] : List FactorBlock).map factorBlockValue).prod) = 7926051476989099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_53
      · exact prime_ninetyNineCS_27737
      · exact prime_ninetyNineCS_299536001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7926051476989099) ^ 3963025738494549 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 7926051476989099) ^ 2642017158996366 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 7926051476989099) ^ 149548141075266 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 7926051476989099) ^ 285757344954 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 7926051476989099) ^ 26461098 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_8141183542718833 : Nat.Prime 8141183542718833 := by
  apply lucas_primality 8141183542718833 (10 : ZMod 8141183542718833)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (31, 1), (311, 1), (1034844997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (31, 1), (311, 1), (1034844997, 1)] : List FactorBlock).map factorBlockValue).prod) = 8141183542718833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_311
      · exact prime_ninetyNineCS_1034844997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8141183542718833) ^ 4070591771359416 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 8141183542718833) ^ 2713727847572944 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 8141183542718833) ^ 478893149571696 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 8141183542718833) ^ 262618823958672 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 8141183542718833) ^ 26177439044112 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (10 : ZMod 8141183542718833) ^ 7867056 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_8537710308260951 : Nat.Prime 8537710308260951 := by
  apply lucas_primality 8537710308260951 (11 : ZMod 8537710308260951)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (79, 1), (1151, 1), (4751, 1), (395261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (79, 1), (1151, 1), (4751, 1), (395261, 1)] : List FactorBlock).map factorBlockValue).prod) = 8537710308260951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_79
      · exact prime_ninetyNineCS_1151
      · exact prime_ninetyNineCS_4751
      · exact prime_ninetyNineCS_395261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 8537710308260951) ^ 4268855154130475 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 8537710308260951) ^ 1707542061652190 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 8537710308260951) ^ 108072282383050 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 8537710308260951) ^ 7417645793450 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 8537710308260951) ^ 1797034373450 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 8537710308260951) ^ 21600183950 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_15572918011191869 : Nat.Prime 15572918011191869 := by
  apply lucas_primality 15572918011191869 (2 : ZMod 15572918011191869)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (173, 1), (487, 1), (116381, 1), (397057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (173, 1), (487, 1), (116381, 1), (397057, 1)] : List FactorBlock).map factorBlockValue).prod) = 15572918011191869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_173
      · exact prime_ninetyNineCS_487
      · exact prime_ninetyNineCS_116381
      · exact prime_ninetyNineCS_397057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15572918011191869) ^ 7786459005595934 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15572918011191869) ^ 90016867116716 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15572918011191869) ^ 31977244376164 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15572918011191869) ^ 133809797228 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15572918011191869) ^ 39220862524 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_23005427962594859 : Nat.Prime 23005427962594859 := by
  apply lucas_primality 23005427962594859 (2 : ZMod 23005427962594859)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (691, 1), (37423, 1), (3676193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (691, 1), (37423, 1), (3676193, 1)] : List FactorBlock).map factorBlockValue).prod) = 23005427962594859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_691
      · exact prime_ninetyNineCS_37423
      · exact prime_ninetyNineCS_3676193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23005427962594859) ^ 11502713981297429 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23005427962594859) ^ 2091402542054078 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23005427962594859) ^ 33292949294638 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23005427962594859) ^ 614740345846 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23005427962594859) ^ 6257948906 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_24094485001966237 : Nat.Prime 24094485001966237 := by
  apply lucas_primality 24094485001966237 (2 : ZMod 24094485001966237)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (151, 1), (18043, 1), (5153647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (151, 1), (18043, 1), (5153647, 1)] : List FactorBlock).map factorBlockValue).prod) = 24094485001966237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_151
      · exact prime_ninetyNineCS_18043
      · exact prime_ninetyNineCS_5153647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24094485001966237) ^ 12047242500983118 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24094485001966237) ^ 8031495000655412 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24094485001966237) ^ 2190407727451476 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24094485001966237) ^ 1853421923228172 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24094485001966237) ^ 159566125840836 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24094485001966237) ^ 1335392396052 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24094485001966237) ^ 4675229988 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_44921431500426643 : Nat.Prime 44921431500426643 := by
  apply lucas_primality 44921431500426643 (2 : ZMod 44921431500426643)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (43, 2), (25150090363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (43, 2), (25150090363, 1)] : List FactorBlock).map factorBlockValue).prod) = 44921431500426643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_23
      · exact prime_ninetyNineCS_43
      · exact prime_ninetyNineCS_25150090363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44921431500426643) ^ 22460715750213321 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44921431500426643) ^ 14973810500142214 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44921431500426643) ^ 6417347357203806 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44921431500426643) ^ 1953105717409854 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44921431500426643) ^ 1044684453498294 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44921431500426643) ^ 1786134 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_45491719151355289 : Nat.Prime 45491719151355289 := by
  apply lucas_primality 45491719151355289 (13 : ZMod 45491719151355289)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 3), (107, 1), (283, 1), (3947, 1), (46237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 3), (107, 1), (283, 1), (3947, 1), (46237, 1)] : List FactorBlock).map factorBlockValue).prod) = 45491719151355289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_107
      · exact prime_ninetyNineCS_283
      · exact prime_ninetyNineCS_3947
      · exact prime_ninetyNineCS_46237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 45491719151355289) ^ 22745859575677644 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 45491719151355289) ^ 15163906383785096 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 45491719151355289) ^ 6498817021622184 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 45491719151355289) ^ 425156253750984 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 45491719151355289) ^ 160748124209736 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 45491719151355289) ^ 11525644578504 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (13 : ZMod 45491719151355289) ^ 983881288824 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_52460035477425011 : Nat.Prime 52460035477425011 := by
  apply lucas_primality 52460035477425011 (2 : ZMod 52460035477425011)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (290471, 1), (1062372643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (290471, 1), (1062372643, 1)] : List FactorBlock).map factorBlockValue).prod) = 52460035477425011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_290471
      · exact prime_ninetyNineCS_1062372643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52460035477425011) ^ 26230017738712505 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 52460035477425011) ^ 10492007095485002 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 52460035477425011) ^ 3085884439848530 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 52460035477425011) ^ 180603349310 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 52460035477425011) ^ 49380070 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_78078731305495561 : Nat.Prime 78078731305495561 := by
  apply lucas_primality 78078731305495561 (17 : ZMod 78078731305495561)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (79, 1), (179, 1), (1831, 1), (25129453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (79, 1), (179, 1), (1831, 1), (25129453, 1)] : List FactorBlock).map factorBlockValue).prod) = 78078731305495561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_79
      · exact prime_ninetyNineCS_179
      · exact prime_ninetyNineCS_1831
      · exact prime_ninetyNineCS_25129453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 78078731305495561) ^ 39039365652747780 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 78078731305495561) ^ 26026243768498520 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 78078731305495561) ^ 15615746261099112 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 78078731305495561) ^ 988338370955640 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 78078731305495561) ^ 436194029639640 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 78078731305495561) ^ 42642671384760 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 78078731305495561) ^ 3107060520 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_104161529215238329 : Nat.Prime 104161529215238329 := by
  apply lucas_primality 104161529215238329 (11 : ZMod 104161529215238329)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (137, 1), (42089, 1), (250891343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (137, 1), (42089, 1), (250891343, 1)] : List FactorBlock).map factorBlockValue).prod) = 104161529215238329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_137
      · exact prime_ninetyNineCS_42089
      · exact prime_ninetyNineCS_250891343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 104161529215238329) ^ 52080764607619164 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 104161529215238329) ^ 34720509738412776 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 104161529215238329) ^ 760303132957944 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 104161529215238329) ^ 2474792207352 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 104161529215238329) ^ 415165896 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_107483305702924999 : Nat.Prime 107483305702924999 := by
  apply lucas_primality 107483305702924999 (3 : ZMod 107483305702924999)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (11, 1), (11078468944849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (11, 1), (11078468944849, 1)] : List FactorBlock).map factorBlockValue).prod) = 107483305702924999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_11078468944849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 107483305702924999) ^ 53741652851462499 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 107483305702924999) ^ 35827768567641666 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 107483305702924999) ^ 15354757957560714 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 107483305702924999) ^ 9771209609356818 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 107483305702924999) ^ 9702 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_218020852156686167 : Nat.Prime 218020852156686167 := by
  apply lucas_primality 218020852156686167 (5 : ZMod 218020852156686167)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (15572918011191869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (15572918011191869, 1)] : List FactorBlock).map factorBlockValue).prod) = 218020852156686167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_15572918011191869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 218020852156686167) ^ 109010426078343083 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 218020852156686167) ^ 31145836022383738 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 218020852156686167) ^ 14 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_293044061755608479 : Nat.Prime 293044061755608479 := by
  apply lucas_primality 293044061755608479 (7 : ZMod 293044061755608479)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3917, 1), (5343813810781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3917, 1), (5343813810781, 1)] : List FactorBlock).map factorBlockValue).prod) = 293044061755608479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_3917
      · exact prime_ninetyNineCS_5343813810781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 293044061755608479) ^ 146522030877804239 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 293044061755608479) ^ 41863437393658354 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 293044061755608479) ^ 74813393350934 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 293044061755608479) ^ 54838 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_340905512333224829 : Nat.Prime 340905512333224829 := by
  apply lucas_primality 340905512333224829 (2 : ZMod 340905512333224829)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (29, 1), (31, 1), (63317, 1), (136113539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (29, 1), (31, 1), (63317, 1), (136113539, 1)] : List FactorBlock).map factorBlockValue).prod) = 340905512333224829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_29
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_63317
      · exact prime_ninetyNineCS_136113539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 340905512333224829) ^ 170452756166612414 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 340905512333224829) ^ 30991410212111348 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 340905512333224829) ^ 11755362494249132 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 340905512333224829) ^ 10996952010749188 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 340905512333224829) ^ 5384107148684 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 340905512333224829) ^ 2504567252 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_584173025748480463 : Nat.Prime 584173025748480463 := by
  apply lucas_primality 584173025748480463 (3 : ZMod 584173025748480463)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (43, 1), (323462361986977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (43, 1), (323462361986977, 1)] : List FactorBlock).map factorBlockValue).prod) = 584173025748480463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_43
      · exact prime_ninetyNineCS_323462361986977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 584173025748480463) ^ 292086512874240231 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 584173025748480463) ^ 194724341916160154 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 584173025748480463) ^ 83453289392640066 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 584173025748480463) ^ 13585419203453034 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 584173025748480463) ^ 1806 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_595967373218987101 : Nat.Prime 595967373218987101 := by
  apply lucas_primality 595967373218987101 (2 : ZMod 595967373218987101)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (19, 2), (611436722293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (19, 2), (611436722293, 1)] : List FactorBlock).map factorBlockValue).prod) = 595967373218987101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_611436722293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 595967373218987101) ^ 297983686609493550 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 595967373218987101) ^ 198655791072995700 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 595967373218987101) ^ 119193474643797420 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 595967373218987101) ^ 31366703853630900 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 595967373218987101) ^ 974700 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_596675319968929561 : Nat.Prime 596675319968929561 := by
  apply lucas_primality 596675319968929561 (7 : ZMod 596675319968929561)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (3361, 1), (1479409203533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (3361, 1), (1479409203533, 1)] : List FactorBlock).map factorBlockValue).prod) = 596675319968929561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_3361
      · exact prime_ninetyNineCS_1479409203533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 596675319968929561) ^ 298337659984464780 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 596675319968929561) ^ 198891773322976520 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 596675319968929561) ^ 119335063993785912 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 596675319968929561) ^ 177529104423960 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 596675319968929561) ^ 403320 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_657992300136899851 : Nat.Prime 657992300136899851 := by
  apply lucas_primality 657992300136899851 (2 : ZMod 657992300136899851)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (41, 1), (838421, 1), (14178851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (41, 1), (838421, 1), (14178851, 1)] : List FactorBlock).map factorBlockValue).prod) = 657992300136899851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_41
      · exact prime_ninetyNineCS_838421
      · exact prime_ninetyNineCS_14178851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 657992300136899851) ^ 328996150068449925 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 657992300136899851) ^ 219330766712299950 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 657992300136899851) ^ 131598460027379970 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 657992300136899851) ^ 16048592686265850 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 657992300136899851) ^ 784799402850 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 657992300136899851) ^ 46406602350 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_910684419114619463 : Nat.Prime 910684419114619463 := by
  apply lucas_primality 910684419114619463 (5 : ZMod 910684419114619463)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (487, 1), (1811, 1), (516286178983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (487, 1), (1811, 1), (516286178983, 1)] : List FactorBlock).map factorBlockValue).prod) = 910684419114619463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_487
      · exact prime_ninetyNineCS_1811
      · exact prime_ninetyNineCS_516286178983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 910684419114619463) ^ 455342209557309731 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 910684419114619463) ^ 1869988540276426 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 910684419114619463) ^ 502862738329442 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 910684419114619463) ^ 1763914 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1179076055475927283 : Nat.Prime 1179076055475927283 := by
  apply lucas_primality 1179076055475927283 (2 : ZMod 1179076055475927283)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (467, 1), (420798021226241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (467, 1), (420798021226241, 1)] : List FactorBlock).map factorBlockValue).prod) = 1179076055475927283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_467
      · exact prime_ninetyNineCS_420798021226241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1179076055475927283) ^ 589538027737963641 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1179076055475927283) ^ 393025351825309094 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1179076055475927283) ^ 2524788127357446 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1179076055475927283) ^ 2802 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1254498623146035857 : Nat.Prime 1254498623146035857 := by
  apply lucas_primality 1254498623146035857 (3 : ZMod 1254498623146035857)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (4612127290978073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (4612127290978073, 1)] : List FactorBlock).map factorBlockValue).prod) = 1254498623146035857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_4612127290978073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1254498623146035857) ^ 627249311573017928 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1254498623146035857) ^ 73794036655649168 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1254498623146035857) ^ 272 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1371233967029624161 : Nat.Prime 1371233967029624161 := by
  apply lucas_primality 1371233967029624161 (17 : ZMod 1371233967029624161)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (730421, 1), (1303694459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (730421, 1), (1303694459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1371233967029624161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_730421
      · exact prime_ninetyNineCS_1303694459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1371233967029624161) ^ 685616983514812080 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 1371233967029624161) ^ 457077989009874720 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 1371233967029624161) ^ 274246793405924832 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 1371233967029624161) ^ 1877320020960 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 1371233967029624161) ^ 1051806240 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_5091301253353824337 : Nat.Prime 5091301253353824337 := by
  apply lucas_primality 5091301253353824337 (5 : ZMod 5091301253353824337)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (25253, 1), (4200244569419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (25253, 1), (4200244569419, 1)] : List FactorBlock).map factorBlockValue).prod) = 5091301253353824337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_25253
      · exact prime_ninetyNineCS_4200244569419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5091301253353824337) ^ 2545650626676912168 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 5091301253353824337) ^ 1697100417784608112 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 5091301253353824337) ^ 201611739332112 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 5091301253353824337) ^ 1212144 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_10127951650833345149 : Nat.Prime 10127951650833345149 := by
  apply lucas_primality 10127951650833345149 (2 : ZMod 10127951650833345149)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1543, 1), (71345710296383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1543, 1), (71345710296383, 1)] : List FactorBlock).map factorBlockValue).prod) = 10127951650833345149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_23
      · exact prime_ninetyNineCS_1543
      · exact prime_ninetyNineCS_71345710296383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10127951650833345149) ^ 5063975825416672574 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10127951650833345149) ^ 440345723949275876 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10127951650833345149) ^ 6563805347267236 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10127951650833345149) ^ 141956 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_10842838420521087433 : Nat.Prime 10842838420521087433 := by
  apply lucas_primality 10842838420521087433 (5 : ZMod 10842838420521087433)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (7926051476989099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (7926051476989099, 1)] : List FactorBlock).map factorBlockValue).prod) = 10842838420521087433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_7926051476989099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10842838420521087433) ^ 5421419210260543716 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 10842838420521087433) ^ 3614279473507029144 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 10842838420521087433) ^ 570675706343215128 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 10842838420521087433) ^ 1368 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_14317516048287507599 : Nat.Prime 14317516048287507599 := by
  apply lucas_primality 14317516048287507599 (11 : ZMod 14317516048287507599)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (383, 1), (439, 1), (803338385459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (383, 1), (439, 1), (803338385459, 1)] : List FactorBlock).map factorBlockValue).prod) = 14317516048287507599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_53
      · exact prime_ninetyNineCS_383
      · exact prime_ninetyNineCS_439
      · exact prime_ninetyNineCS_803338385459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 14317516048287507599) ^ 7158758024143753799 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 14317516048287507599) ^ 270141812231839766 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 14317516048287507599) ^ 37382548428949106 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 14317516048287507599) ^ 32613931772864482 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 14317516048287507599) ^ 17822522 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_16644333730688624053 : Nat.Prime 16644333730688624053 := by
  apply lucas_primality 16644333730688624053 (2 : ZMod 16644333730688624053)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (97, 1), (3643, 1), (46181, 1), (28331507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (97, 1), (3643, 1), (46181, 1), (28331507, 1)] : List FactorBlock).map factorBlockValue).prod) = 16644333730688624053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_97
      · exact prime_ninetyNineCS_3643
      · exact prime_ninetyNineCS_46181
      · exact prime_ninetyNineCS_28331507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16644333730688624053) ^ 8322166865344312026 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16644333730688624053) ^ 5548111243562874684 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16644333730688624053) ^ 171591069388542516 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16644333730688624053) ^ 4568853618086364 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16644333730688624053) ^ 360415186563492 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16644333730688624053) ^ 587484941436 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_18249489080724596333 : Nat.Prime 18249489080724596333 := by
  apply lucas_primality 18249489080724596333 (2 : ZMod 18249489080724596333)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (1733, 1), (3401807, 1), (6395833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (1733, 1), (3401807, 1), (6395833, 1)] : List FactorBlock).map factorBlockValue).prod) = 18249489080724596333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_1733
      · exact prime_ninetyNineCS_3401807
      · exact prime_ninetyNineCS_6395833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18249489080724596333) ^ 9124744540362298166 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18249489080724596333) ^ 1659044461884054212 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18249489080724596333) ^ 10530576503591804 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18249489080724596333) ^ 5364645637076 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18249489080724596333) ^ 2853340461004 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_22505732643611106443 : Nat.Prime 22505732643611106443 := by
  apply lucas_primality 22505732643611106443 (2 : ZMod 22505732643611106443)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (121501, 1), (13230774493103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (121501, 1), (13230774493103, 1)] : List FactorBlock).map factorBlockValue).prod) = 22505732643611106443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_121501
      · exact prime_ninetyNineCS_13230774493103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22505732643611106443) ^ 11252866321805553221 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 22505732643611106443) ^ 3215104663373015206 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 22505732643611106443) ^ 185230842903442 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 22505732643611106443) ^ 1701014 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_56560638772389428983 : Nat.Prime 56560638772389428983 := by
  apply lucas_primality 56560638772389428983 (3 : ZMod 56560638772389428983)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1150109341, 1), (2732138239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1150109341, 1), (2732138239, 1)] : List FactorBlock).map factorBlockValue).prod) = 56560638772389428983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_1150109341
      · exact prime_ninetyNineCS_2732138239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56560638772389428983) ^ 28280319386194714491 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 56560638772389428983) ^ 18853546257463142994 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 56560638772389428983) ^ 49178488302 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 56560638772389428983) ^ 20701968138 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_77964977642002133471 : Nat.Prime 77964977642002133471 := by
  apply lucas_primality 77964977642002133471 (17 : ZMod 77964977642002133471)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (31, 1), (83, 1), (317, 1), (503091418393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (31, 1), (83, 1), (317, 1), (503091418393, 1)] : List FactorBlock).map factorBlockValue).prod) = 77964977642002133471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_83
      · exact prime_ninetyNineCS_317
      · exact prime_ninetyNineCS_503091418393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 77964977642002133471) ^ 38982488821001066735 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 77964977642002133471) ^ 15592995528400426694 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 77964977642002133471) ^ 4103419875894849130 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 77964977642002133471) ^ 2514999278774262370 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 77964977642002133471) ^ 939337080024122090 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 77964977642002133471) ^ 245946301709785910 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 77964977642002133471) ^ 154971790 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_108428384205210874331 : Nat.Prime 108428384205210874331 := by
  apply lucas_primality 108428384205210874331 (2 : ZMod 108428384205210874331)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10842838420521087433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10842838420521087433, 1)] : List FactorBlock).map factorBlockValue).prod) = 108428384205210874331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_10842838420521087433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 108428384205210874331) ^ 54214192102605437165 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 108428384205210874331) ^ 21685676841042174866 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 108428384205210874331) ^ 10 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_111552471583795651571 : Nat.Prime 111552471583795651571 := by
  apply lucas_primality 111552471583795651571 (6 : ZMod 111552471583795651571)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (271, 1), (617, 1), (59707, 1), (159625199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (271, 1), (617, 1), (59707, 1), (159625199, 1)] : List FactorBlock).map factorBlockValue).prod) = 111552471583795651571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_271
      · exact prime_ninetyNineCS_617
      · exact prime_ninetyNineCS_59707
      · exact prime_ninetyNineCS_159625199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 111552471583795651571) ^ 55776235791897825785 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 111552471583795651571) ^ 22310494316759130314 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 111552471583795651571) ^ 15936067369113664510 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 111552471583795651571) ^ 411632736471570670 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 111552471583795651571) ^ 180798171124466210 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 111552471583795651571) ^ 1868331545443510 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 111552471583795651571) ^ 698839984430 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_138498501910441436191 : Nat.Prime 138498501910441436191 := by
  apply lucas_primality 138498501910441436191 (3 : ZMod 138498501910441436191)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (29, 1), (887, 1), (87977, 1), (97143503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (29, 1), (887, 1), (87977, 1), (97143503, 1)] : List FactorBlock).map factorBlockValue).prod) = 138498501910441436191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_29
      · exact prime_ninetyNineCS_887
      · exact prime_ninetyNineCS_87977
      · exact prime_ninetyNineCS_97143503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 138498501910441436191) ^ 69249250955220718095 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 138498501910441436191) ^ 46166167303480478730 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 138498501910441436191) ^ 27699700382088287238 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 138498501910441436191) ^ 19785500272920205170 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 138498501910441436191) ^ 4775810410704877110 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 138498501910441436191) ^ 156142617711884370 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 138498501910441436191) ^ 1574258066431470 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 138498501910441436191) ^ 1425710393730 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_207991370074170734351 : Nat.Prime 207991370074170734351 := by
  apply lucas_primality 207991370074170734351 (17 : ZMod 207991370074170734351)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (19, 1), (31, 1), (73, 1), (397897, 1), (18703511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (19, 1), (31, 1), (73, 1), (397897, 1), (18703511, 1)] : List FactorBlock).map factorBlockValue).prod) = 207991370074170734351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_19
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_73
      · exact prime_ninetyNineCS_397897
      · exact prime_ninetyNineCS_18703511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 207991370074170734351) ^ 103995685037085367175 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 207991370074170734351) ^ 41598274014834146870 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 207991370074170734351) ^ 15999336159551594950 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 207991370074170734351) ^ 10946914214430038650 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 207991370074170734351) ^ 6709399034650668850 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 207991370074170734351) ^ 2849196850331105950 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 207991370074170734351) ^ 522726660603550 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (17 : ZMod 207991370074170734351) ^ 11120445250850 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_239097451688377947647 : Nat.Prime 239097451688377947647 := by
  apply lucas_primality 239097451688377947647 (5 : ZMod 239097451688377947647)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (16603, 1), (423554658244573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (16603, 1), (423554658244573, 1)] : List FactorBlock).map factorBlockValue).prod) = 239097451688377947647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_16603
      · exact prime_ninetyNineCS_423554658244573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 239097451688377947647) ^ 119548725844188973823 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 239097451688377947647) ^ 14064555981669291038 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 239097451688377947647) ^ 14400858380315482 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 239097451688377947647) ^ 564502 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_350845088141730581869 : Nat.Prime 350845088141730581869 := by
  apply lucas_primality 350845088141730581869 (2 : ZMod 350845088141730581869)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (596675319968929561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (596675319968929561, 1)] : List FactorBlock).map factorBlockValue).prod) = 350845088141730581869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_596675319968929561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 350845088141730581869) ^ 175422544070865290934 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 350845088141730581869) ^ 116948362713910193956 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 350845088141730581869) ^ 50120726877390083124 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 350845088141730581869) ^ 588 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_565393172578762817803 : Nat.Prime 565393172578762817803 := by
  apply lucas_primality 565393172578762817803 (2 : ZMod 565393172578762817803)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (257, 1), (401, 1), (743, 1), (6703, 1), (183596239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (257, 1), (401, 1), (743, 1), (6703, 1), (183596239, 1)] : List FactorBlock).map factorBlockValue).prod) = 565393172578762817803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_257
      · exact prime_ninetyNineCS_401
      · exact prime_ninetyNineCS_743
      · exact prime_ninetyNineCS_6703
      · exact prime_ninetyNineCS_183596239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 565393172578762817803) ^ 282696586289381408901 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 565393172578762817803) ^ 188464390859587605934 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 565393172578762817803) ^ 2199973434158610186 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 565393172578762817803) ^ 1409958036356017002 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 565393172578762817803) ^ 760959855422291814 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 565393172578762817803) ^ 84349272352493334 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 565393172578762817803) ^ 3079546594518 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1244334052992567437627 : Nat.Prime 1244334052992567437627 := by
  apply lucas_primality 1244334052992567437627 (2 : ZMod 1244334052992567437627)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (56560638772389428983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (56560638772389428983, 1)] : List FactorBlock).map factorBlockValue).prod) = 1244334052992567437627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_56560638772389428983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1244334052992567437627) ^ 622167026496283718813 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1244334052992567437627) ^ 113121277544778857966 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1244334052992567437627) ^ 22 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2274934485395486328151 : Nat.Prime 2274934485395486328151 := by
  apply lucas_primality 2274934485395486328151 (6 : ZMod 2274934485395486328151)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (227743, 1), (6053965096477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (227743, 1), (6053965096477, 1)] : List FactorBlock).map factorBlockValue).prod) = 2274934485395486328151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_227743
      · exact prime_ninetyNineCS_6053965096477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2274934485395486328151) ^ 1137467242697743164075 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 2274934485395486328151) ^ 758311495131828776050 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 2274934485395486328151) ^ 454986897079097265630 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 2274934485395486328151) ^ 206812225945044211650 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 2274934485395486328151) ^ 9989042409187050 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 2274934485395486328151) ^ 375775950 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_4015888977016643456557 : Nat.Prime 4015888977016643456557 := by
  apply lucas_primality 4015888977016643456557 (2 : ZMod 4015888977016643456557)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (111552471583795651571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (111552471583795651571, 1)] : List FactorBlock).map factorBlockValue).prod) = 4015888977016643456557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_111552471583795651571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4015888977016643456557) ^ 2007944488508321728278 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4015888977016643456557) ^ 1338629659005547818852 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4015888977016643456557) ^ 36 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_7529948591010917889709 : Nat.Prime 7529948591010917889709 := by
  apply lucas_primality 7529948591010917889709 (6 : ZMod 7529948591010917889709)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (991, 1), (44574419, 1), (430464637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (991, 1), (44574419, 1), (430464637, 1)] : List FactorBlock).map factorBlockValue).prod) = 7529948591010917889709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_991
      · exact prime_ninetyNineCS_44574419
      · exact prime_ninetyNineCS_430464637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7529948591010917889709) ^ 3764974295505458944854 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 7529948591010917889709) ^ 2509982863670305963236 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 7529948591010917889709) ^ 684540781000992535428 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 7529948591010917889709) ^ 7598333593351077588 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 7529948591010917889709) ^ 168929820285732 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 7529948591010917889709) ^ 17492606694684 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_7880051983634524559339 : Nat.Prime 7880051983634524559339 := by
  apply lucas_primality 7880051983634524559339 (2 : ZMod 7880051983634524559339)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2293, 1), (175859, 1), (230369, 1), (3855793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2293, 1), (175859, 1), (230369, 1), (3855793, 1)] : List FactorBlock).map factorBlockValue).prod) = 7880051983634524559339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_2293
      · exact prime_ninetyNineCS_175859
      · exact prime_ninetyNineCS_230369
      · exact prime_ninetyNineCS_3855793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7880051983634524559339) ^ 3940025991817262279669 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7880051983634524559339) ^ 716368362148593141758 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7880051983634524559339) ^ 3436568680172056066 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7880051983634524559339) ^ 44808920690067182 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7880051983634524559339) ^ 34206216911279402 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7880051983634524559339) ^ 2043691656589066 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_12256010419956628103887 : Nat.Prime 12256010419956628103887 := by
  apply lucas_primality 12256010419956628103887 (11 : ZMod 12256010419956628103887)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2218609, 1), (4228313, 1), (217745893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2218609, 1), (4228313, 1), (217745893, 1)] : List FactorBlock).map factorBlockValue).prod) = 12256010419956628103887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_2218609
      · exact prime_ninetyNineCS_4228313
      · exact prime_ninetyNineCS_217745893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 12256010419956628103887) ^ 6128005209978314051943 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 12256010419956628103887) ^ 4085336806652209367962 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 12256010419956628103887) ^ 5524186740411054 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 12256010419956628103887) ^ 2898557987537022 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 12256010419956628103887) ^ 56285839659702 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_38014876534651186761691 : Nat.Prime 38014876534651186761691 := by
  apply lucas_primality 38014876534651186761691 (3 : ZMod 38014876534651186761691)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (58652767, 1), (1964043666679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (58652767, 1), (1964043666679, 1)] : List FactorBlock).map factorBlockValue).prod) = 38014876534651186761691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_58652767
      · exact prime_ninetyNineCS_1964043666679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38014876534651186761691) ^ 19007438267325593380845 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38014876534651186761691) ^ 12671625511550395587230 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38014876534651186761691) ^ 7602975306930237352338 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38014876534651186761691) ^ 3455897866786471523790 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38014876534651186761691) ^ 648134410004070 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 38014876534651186761691) ^ 19355413110 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_47603667070878312266317 : Nat.Prime 47603667070878312266317 := by
  apply lucas_primality 47603667070878312266317 (6 : ZMod 47603667070878312266317)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (577, 1), (114481453, 1), (6672763117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (577, 1), (114481453, 1), (6672763117, 1)] : List FactorBlock).map factorBlockValue).prod) = 47603667070878312266317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_577
      · exact prime_ninetyNineCS_114481453
      · exact prime_ninetyNineCS_6672763117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 47603667070878312266317) ^ 23801833535439156133158 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 47603667070878312266317) ^ 15867889023626104088772 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 47603667070878312266317) ^ 82502022653168652108 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 47603667070878312266317) ^ 415819906398972 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 47603667070878312266317) ^ 7134026225148 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_79040649647308215205853 : Nat.Prime 79040649647308215205853 := by
  apply lucas_primality 79040649647308215205853 (2 : ZMod 79040649647308215205853)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (211, 1), (533620211, 1), (2974567117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (211, 1), (533620211, 1), (2974567117, 1)] : List FactorBlock).map factorBlockValue).prod) = 79040649647308215205853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_59
      · exact prime_ninetyNineCS_211
      · exact prime_ninetyNineCS_533620211
      · exact prime_ninetyNineCS_2974567117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79040649647308215205853) ^ 39520324823654107602926 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 79040649647308215205853) ^ 1339672027920478223828 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 79040649647308215205853) ^ 374600235295299598132 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 79040649647308215205853) ^ 148121544158132 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 79040649647308215205853) ^ 26572152026956 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_106818767711888085542707 : Nat.Prime 106818767711888085542707 := by
  apply lucas_primality 106818767711888085542707 (2 : ZMod 106818767711888085542707)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4813, 1), (600371, 1), (6161135288837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4813, 1), (600371, 1), (6161135288837, 1)] : List FactorBlock).map factorBlockValue).prod) = 106818767711888085542707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_4813
      · exact prime_ninetyNineCS_600371
      · exact prime_ninetyNineCS_6161135288837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 106818767711888085542707) ^ 53409383855944042771353 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 106818767711888085542707) ^ 35606255903962695180902 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 106818767711888085542707) ^ 22193801726966151162 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 106818767711888085542707) ^ 177921264871034886 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 106818767711888085542707) ^ 17337513738 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_112928297992645484807863 : Nat.Prime 112928297992645484807863 := by
  apply lucas_primality 112928297992645484807863 (3 : ZMod 112928297992645484807863)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4859249, 1), (18808877, 1), (205929949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4859249, 1), (18808877, 1), (205929949, 1)] : List FactorBlock).map factorBlockValue).prod) = 112928297992645484807863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_4859249
      · exact prime_ninetyNineCS_18808877
      · exact prime_ninetyNineCS_205929949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 112928297992645484807863) ^ 56464148996322742403931 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 112928297992645484807863) ^ 37642765997548494935954 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 112928297992645484807863) ^ 23239866488143638 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 112928297992645484807863) ^ 6003989392489806 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 112928297992645484807863) ^ 548382100520238 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_327378668399472533239049 : Nat.Prime 327378668399472533239049 := by
  apply lucas_primality 327378668399472533239049 (3 : ZMod 327378668399472533239049)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3170638223, 1), (12906654960847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3170638223, 1), (12906654960847, 1)] : List FactorBlock).map factorBlockValue).prod) = 327378668399472533239049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3170638223
      · exact prime_ninetyNineCS_12906654960847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 327378668399472533239049) ^ 163689334199736266619524 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 327378668399472533239049) ^ 103253239686776 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 327378668399472533239049) ^ 25365105784 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_389330477750655024726823 : Nat.Prime 389330477750655024726823 := by
  apply lucas_primality 389330477750655024726823 (3 : ZMod 389330477750655024726823)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (45319, 1), (509449, 1), (2810516374927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (45319, 1), (509449, 1), (2810516374927, 1)] : List FactorBlock).map factorBlockValue).prod) = 389330477750655024726823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_45319
      · exact prime_ninetyNineCS_509449
      · exact prime_ninetyNineCS_2810516374927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 389330477750655024726823) ^ 194665238875327512363411 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 389330477750655024726823) ^ 129776825916885008242274 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 389330477750655024726823) ^ 8590888540141111338 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 389330477750655024726823) ^ 764218749571900278 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 389330477750655024726823) ^ 138526315386 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_463781041828186472574493 : Nat.Prime 463781041828186472574493 := by
  apply lucas_primality 463781041828186472574493 (2 : ZMod 463781041828186472574493)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (53, 1), (4397, 1), (25793, 1), (27953, 1), (2987297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (53, 1), (4397, 1), (25793, 1), (27953, 1), (2987297, 1)] : List FactorBlock).map factorBlockValue).prod) = 463781041828186472574493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_53
      · exact prime_ninetyNineCS_4397
      · exact prime_ninetyNineCS_25793
      · exact prime_ninetyNineCS_27953
      · exact prime_ninetyNineCS_2987297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 463781041828186472574493) ^ 231890520914093236287246 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 463781041828186472574493) ^ 154593680609395490858164 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 463781041828186472574493) ^ 66254434546883781796356 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 463781041828186472574493) ^ 42161912893471497506772 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 463781041828186472574493) ^ 8750585694871442878764 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 463781041828186472574493) ^ 105476698164245274636 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 463781041828186472574493) ^ 17980887908664617244 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 463781041828186472574493) ^ 16591458585060153564 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 463781041828186472574493) ^ 155251065370529436 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_487900579114856645366807 : Nat.Prime 487900579114856645366807 := by
  apply lucas_primality 487900579114856645366807 (5 : ZMod 487900579114856645366807)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (39451, 1), (4053503, 1), (1525502146351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (39451, 1), (4053503, 1), (1525502146351, 1)] : List FactorBlock).map factorBlockValue).prod) = 487900579114856645366807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_39451
      · exact prime_ninetyNineCS_4053503
      · exact prime_ninetyNineCS_1525502146351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 487900579114856645366807) ^ 243950289557428322683403 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 487900579114856645366807) ^ 12367255053480435106 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 487900579114856645366807) ^ 120365170351386602 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 487900579114856645366807) ^ 319829493706 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1278140318498475769144351 : Nat.Prime 1278140318498475769144351 := by
  apply lucas_primality 1278140318498475769144351 (3 : ZMod 1278140318498475769144351)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1359509, 1), (6267656526478681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1359509, 1), (6267656526478681, 1)] : List FactorBlock).map factorBlockValue).prod) = 1278140318498475769144351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_1359509
      · exact prime_ninetyNineCS_6267656526478681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1278140318498475769144351) ^ 639070159249237884572175 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1278140318498475769144351) ^ 426046772832825256381450 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1278140318498475769144351) ^ 255628063699695153828870 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1278140318498475769144351) ^ 940148478971802150 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1278140318498475769144351) ^ 203926350 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1393286450089034355684413 : Nat.Prime 1393286450089034355684413 := by
  apply lucas_primality 1393286450089034355684413 (2 : ZMod 1393286450089034355684413)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (4549, 1), (3803879, 1), (1829974788463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (4549, 1), (3803879, 1), (1829974788463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1393286450089034355684413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_4549
      · exact prime_ninetyNineCS_3803879
      · exact prime_ninetyNineCS_1829974788463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1393286450089034355684413) ^ 696643225044517177842206 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1393286450089034355684413) ^ 126662404553548577789492 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1393286450089034355684413) ^ 306284117408009310988 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1393286450089034355684413) ^ 366280433759600228 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1393286450089034355684413) ^ 761369205124 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2462693238078974479424849 : Nat.Prime 2462693238078974479424849 := by
  apply lucas_primality 2462693238078974479424849 (3 : ZMod 2462693238078974479424849)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (89, 1), (19660932391, 1), (87962227547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (89, 1), (19660932391, 1), (87962227547, 1)] : List FactorBlock).map factorBlockValue).prod) = 2462693238078974479424849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_89
      · exact prime_ninetyNineCS_19660932391
      · exact prime_ninetyNineCS_87962227547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2462693238078974479424849) ^ 1231346619039487239712424 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2462693238078974479424849) ^ 27670710540213196398032 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2462693238078974479424849) ^ 125258212026928 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2462693238078974479424849) ^ 27997167724784 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_4253995112531054011907567 : Nat.Prime 4253995112531054011907567 := by
  apply lucas_primality 4253995112531054011907567 (5 : ZMod 4253995112531054011907567)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1901, 1), (109891261, 1), (925612118573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1901, 1), (109891261, 1), (925612118573, 1)] : List FactorBlock).map factorBlockValue).prod) = 4253995112531054011907567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_11
      · exact prime_ninetyNineCS_1901
      · exact prime_ninetyNineCS_109891261
      · exact prime_ninetyNineCS_925612118573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4253995112531054011907567) ^ 2126997556265527005953783 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 4253995112531054011907567) ^ 386726828411914001082506 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 4253995112531054011907567) ^ 2237767023951106792166 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 4253995112531054011907567) ^ 38710950022960006 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 4253995112531054011907567) ^ 4595872317542 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_5708927008398176767321471 : Nat.Prime 5708927008398176767321471 := by
  apply lucas_primality 5708927008398176767321471 (6 : ZMod 5708927008398176767321471)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (4153, 1), (5091301253353824337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (4153, 1), (5091301253353824337, 1)] : List FactorBlock).map factorBlockValue).prod) = 5708927008398176767321471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_4153
      · exact prime_ninetyNineCS_5091301253353824337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5708927008398176767321471) ^ 2854463504199088383660735 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5708927008398176767321471) ^ 1902975669466058922440490 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5708927008398176767321471) ^ 1141785401679635353464294 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5708927008398176767321471) ^ 1374651338405532570990 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (6 : ZMod 5708927008398176767321471) ^ 1121310 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_16909046738829734192953597 : Nat.Prime 16909046738829734192953597 := by
  apply lucas_primality 16909046738829734192953597 (5 : ZMod 16909046738829734192953597)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (30781737289, 1), (15258909473999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (30781737289, 1), (15258909473999, 1)] : List FactorBlock).map factorBlockValue).prod) = 16909046738829734192953597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_30781737289
      · exact prime_ninetyNineCS_15258909473999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16909046738829734192953597) ^ 8454523369414867096476798 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 16909046738829734192953597) ^ 5636348912943244730984532 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 16909046738829734192953597) ^ 549320741063964 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 16909046738829734192953597) ^ 1108142542404 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_43269656756443408533687541 : Nat.Prime 43269656756443408533687541 := by
  apply lucas_primality 43269656756443408533687541 (2 : ZMod 43269656756443408533687541)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1617019, 1), (80038859, 1), (5572065179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1617019, 1), (80038859, 1), (5572065179, 1)] : List FactorBlock).map factorBlockValue).prod) = 43269656756443408533687541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_1617019
      · exact prime_ninetyNineCS_80038859
      · exact prime_ninetyNineCS_5572065179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43269656756443408533687541) ^ 21634828378221704266843770 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43269656756443408533687541) ^ 14423218918814469511229180 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43269656756443408533687541) ^ 8653931351288681706737508 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43269656756443408533687541) ^ 26758904352047445660 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43269656756443408533687541) ^ 540608115820884060 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43269656756443408533687541) ^ 7765461344479260 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_62092531313623034527121909 : Nat.Prime 62092531313623034527121909 := by
  apply lucas_primality 62092531313623034527121909 (2 : ZMod 62092531313623034527121909)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (36670704067, 1), (3746119971887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (36670704067, 1), (3746119971887, 1)] : List FactorBlock).map factorBlockValue).prod) = 62092531313623034527121909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_113
      · exact prime_ninetyNineCS_36670704067
      · exact prime_ninetyNineCS_3746119971887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 62092531313623034527121909) ^ 31046265656811517263560954 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 62092531313623034527121909) ^ 549491427554186146257716 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 62092531313623034527121909) ^ 1693246227292924 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 62092531313623034527121909) ^ 16575158238284 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_72879465458393163190301867 : Nat.Prime 72879465458393163190301867 := by
  apply lucas_primality 72879465458393163190301867 (2 : ZMod 72879465458393163190301867)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1009, 1), (5039, 1), (10501, 1), (682509969998383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1009, 1), (5039, 1), (10501, 1), (682509969998383, 1)] : List FactorBlock).map factorBlockValue).prod) = 72879465458393163190301867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_1009
      · exact prime_ninetyNineCS_5039
      · exact prime_ninetyNineCS_10501
      · exact prime_ninetyNineCS_682509969998383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 72879465458393163190301867) ^ 36439732729196581595150933 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 72879465458393163190301867) ^ 72229400850736534380874 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 72879465458393163190301867) ^ 14463081059415194123894 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 72879465458393163190301867) ^ 6940240496942497208866 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 72879465458393163190301867) ^ 106781539702 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_81849245822503090967569789 : Nat.Prime 81849245822503090967569789 := by
  apply lucas_primality 81849245822503090967569789 (2 : ZMod 81849245822503090967569789)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (41, 1), (46817, 1), (7458931, 1), (52933047623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (41, 1), (46817, 1), (7458931, 1), (52933047623, 1)] : List FactorBlock).map factorBlockValue).prod) = 81849245822503090967569789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_41
      · exact prime_ninetyNineCS_46817
      · exact prime_ninetyNineCS_7458931
      · exact prime_ninetyNineCS_52933047623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 81849245822503090967569789) ^ 40924622911251545483784894 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 81849245822503090967569789) ^ 27283081940834363655856596 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 81849245822503090967569789) ^ 1996323068841538804087068 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 81849245822503090967569789) ^ 1748280449890063245564 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 81849245822503090967569789) ^ 10973321220226208148 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 81849245822503090967569789) ^ 1546278733192356 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_234088843052358840167249597 : Nat.Prime 234088843052358840167249597 := by
  apply lucas_primality 234088843052358840167249597 (2 : ZMod 234088843052358840167249597)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (503, 1), (13147, 1), (22751, 1), (43037, 1), (531660841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (503, 1), (13147, 1), (22751, 1), (43037, 1), (531660841, 1)] : List FactorBlock).map factorBlockValue).prod) = 234088843052358840167249597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_503
      · exact prime_ninetyNineCS_13147
      · exact prime_ninetyNineCS_22751
      · exact prime_ninetyNineCS_43037
      · exact prime_ninetyNineCS_531660841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 234088843052358840167249597) ^ 117044421526179420083624798 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 234088843052358840167249597) ^ 13769931944256402362779388 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 234088843052358840167249597) ^ 465385373861548389994532 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 234088843052358840167249597) ^ 17805495021857369754868 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 234088843052358840167249597) ^ 10289167203743081190596 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 234088843052358840167249597) ^ 5439246300912211356908 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 234088843052358840167249597) ^ 440297319268542556 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_308011635595209000220065259 : Nat.Prime 308011635595209000220065259 := by
  apply lucas_primality 308011635595209000220065259 (2 : ZMod 308011635595209000220065259)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (31, 1), (67, 1), (1537639, 1), (2296291140731683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (31, 1), (67, 1), (1537639, 1), (2296291140731683, 1)] : List FactorBlock).map factorBlockValue).prod) = 308011635595209000220065259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_7
      · exact prime_ninetyNineCS_31
      · exact prime_ninetyNineCS_67
      · exact prime_ninetyNineCS_1537639
      · exact prime_ninetyNineCS_2296291140731683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 308011635595209000220065259) ^ 154005817797604500110032629 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 308011635595209000220065259) ^ 102670545198403000073355086 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 308011635595209000220065259) ^ 44001662227887000031437894 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 308011635595209000220065259) ^ 9935859212748677426453718 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 308011635595209000220065259) ^ 4597188590973268660000974 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 308011635595209000220065259) ^ 200314661370587634822 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 308011635595209000220065259) ^ 134134400526 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_522519738956158125373324993 : Nat.Prime 522519738956158125373324993 := by
  apply lucas_primality 522519738956158125373324993 (7 : ZMod 522519738956158125373324993)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (1277, 1), (29483, 1), (24094485001966237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (1277, 1), (29483, 1), (24094485001966237, 1)] : List FactorBlock).map factorBlockValue).prod) = 522519738956158125373324993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_1277
      · exact prime_ninetyNineCS_29483
      · exact prime_ninetyNineCS_24094485001966237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 522519738956158125373324993) ^ 261259869478079062686662496 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 522519738956158125373324993) ^ 174173246318719375124441664 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 522519738956158125373324993) ^ 409177555956271045711296 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 522519738956158125373324993) ^ 17722746632166269557824 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (7 : ZMod 522519738956158125373324993) ^ 21686279616 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_818492458225030909675697891 : Nat.Prime 818492458225030909675697891 := by
  apply lucas_primality 818492458225030909675697891 (2 : ZMod 818492458225030909675697891)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (81849245822503090967569789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (81849245822503090967569789, 1)] : List FactorBlock).map factorBlockValue).prod) = 818492458225030909675697891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_81849245822503090967569789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 818492458225030909675697891) ^ 409246229112515454837848945 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 818492458225030909675697891) ^ 163698491645006181935139578 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 818492458225030909675697891) ^ 10 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_1581681371975397568697632411 : Nat.Prime 1581681371975397568697632411 := by
  apply lucas_primality 1581681371975397568697632411 (2 : ZMod 1581681371975397568697632411)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (59, 1), (13729, 1), (16187, 1), (236532891212363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (59, 1), (13729, 1), (16187, 1), (236532891212363, 1)] : List FactorBlock).map factorBlockValue).prod) = 1581681371975397568697632411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_17
      · exact prime_ninetyNineCS_59
      · exact prime_ninetyNineCS_13729
      · exact prime_ninetyNineCS_16187
      · exact prime_ninetyNineCS_236532891212363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1581681371975397568697632411) ^ 790840685987698784348816205 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581681371975397568697632411) ^ 527227123991799189565877470 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581681371975397568697632411) ^ 316336274395079513739526482 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581681371975397568697632411) ^ 93040080704435151099860730 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581681371975397568697632411) ^ 26808158847040636757586990 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581681371975397568697632411) ^ 115207325513540503219290 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581681371975397568697632411) ^ 97713064309346856656430 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1581681371975397568697632411) ^ 6686940509070 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_2926110538154485502090619961 : Nat.Prime 2926110538154485502090619961 := by
  apply lucas_primality 2926110538154485502090619961 (11 : ZMod 2926110538154485502090619961)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (1163, 1), (1877, 1), (2017, 1), (426006518330923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (1163, 1), (1877, 1), (2017, 1), (426006518330923, 1)] : List FactorBlock).map factorBlockValue).prod) = 2926110538154485502090619961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_13
      · exact prime_ninetyNineCS_1163
      · exact prime_ninetyNineCS_1877
      · exact prime_ninetyNineCS_2017
      · exact prime_ninetyNineCS_426006518330923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2926110538154485502090619961) ^ 1463055269077242751045309980 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 2926110538154485502090619961) ^ 975370179384828500696873320 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 2926110538154485502090619961) ^ 585222107630897100418123992 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 2926110538154485502090619961) ^ 225085426011883500160816920 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 2926110538154485502090619961) ^ 2516002182420021927850920 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 2926110538154485502090619961) ^ 1558929428958170219547480 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 2926110538154485502090619961) ^ 1450724114107330442285880 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (11 : ZMod 2926110538154485502090619961) ^ 6868698980520 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_4180157911649265002986599943 : Nat.Prime 4180157911649265002986599943 := by
  apply lucas_primality 4180157911649265002986599943 (3 : ZMod 4180157911649265002986599943)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29587, 1), (39511, 1), (595967373218987101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29587, 1), (39511, 1), (595967373218987101, 1)] : List FactorBlock).map factorBlockValue).prod) = 4180157911649265002986599943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_29587
      · exact prime_ninetyNineCS_39511
      · exact prime_ninetyNineCS_595967373218987101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4180157911649265002986599943) ^ 2090078955824632501493299971 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4180157911649265002986599943) ^ 1393385970549755000995533314 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4180157911649265002986599943) ^ 141283601299532396085666 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4180157911649265002986599943) ^ 105797320028581028143722 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4180157911649265002986599943) ^ 7014071742 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_9753701793848285006968733207 : Nat.Prime 9753701793848285006968733207 := by
  apply lucas_primality 9753701793848285006968733207 (5 : ZMod 9753701793848285006968733207)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347, 1), (53113, 1), (8408143, 1), (31470894077911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347, 1), (53113, 1), (8408143, 1), (31470894077911, 1)] : List FactorBlock).map factorBlockValue).prod) = 9753701793848285006968733207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_347
      · exact prime_ninetyNineCS_53113
      · exact prime_ninetyNineCS_8408143
      · exact prime_ninetyNineCS_31470894077911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9753701793848285006968733207) ^ 4876850896924142503484366603 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 9753701793848285006968733207) ^ 28108650702732809818353698 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 9753701793848285006968733207) ^ 183640573754980607515462 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 9753701793848285006968733207) ^ 1160030436429100338442 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (5 : ZMod 9753701793848285006968733207) ^ 309927699216346 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_117044421526179420083624798431 : Nat.Prime 117044421526179420083624798431 := by
  apply lucas_primality 117044421526179420083624798431 (3 : ZMod 117044421526179420083624798431)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (49968546521, 1), (78078731305495561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (49968546521, 1), (78078731305495561, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_3
      · exact prime_ninetyNineCS_5
      · exact prime_ninetyNineCS_49968546521
      · exact prime_ninetyNineCS_78078731305495561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 117044421526179420083624798431) ^ 58522210763089710041812399215 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 117044421526179420083624798431) ^ 39014807175393140027874932810 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 117044421526179420083624798431) ^ 23408884305235884016724959686 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 117044421526179420083624798431) ^ 2342361939164866830 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (3 : ZMod 117044421526179420083624798431) ^ 1499056395630 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem prime_ninetyNineCS_117044421526179420083624798483 : Nat.Prime 117044421526179420083624798483 := by
  apply lucas_primality 117044421526179420083624798483 (2 : ZMod 117044421526179420083624798483)
  · rw [← ninetyNineCSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (76910429, 1), (1792284803, 1), (4376800319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (76910429, 1), (1792284803, 1), (4376800319, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyNineCS_2
      · exact prime_ninetyNineCS_97
      · exact prime_ninetyNineCS_76910429
      · exact prime_ninetyNineCS_1792284803
      · exact prime_ninetyNineCS_4376800319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 117044421526179420083624798483) ^ 58522210763089710041812399241 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 117044421526179420083624798483) ^ 1206643520888447629728090706 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 117044421526179420083624798483) ^ 1521827703316794918458 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 117044421526179420083624798483) ^ 65304588495235609094 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide
    · change (2 : ZMod 117044421526179420083624798483) ^ 26742006259248634478 ≠ 1
      rw [← ninetyNineCSFastPow_eq_pow]
      decide

private theorem phi_ninetyNineCS_117044421526179420083624798400 : Nat.totient 117044421526179420083624798400 = 28756561156881383841021296640 := by
  rw [← show ((([(2, 6), (3, 1), (5, 2), (13, 1), (1163, 1), (1877, 1), (2017, 1), (426006518330923, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_5, prime_ninetyNineCS_13, prime_ninetyNineCS_1163, prime_ninetyNineCS_1877, prime_ninetyNineCS_2017, prime_ninetyNineCS_426006518330923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798401 : Nat.totient 117044421526179420083624798401 = 110881557415342605011898684816 := by
  rw [← show ((([(19, 1), (42139, 1), (14143645819, 1), (10335976687219, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_19, prime_ninetyNineCS_42139, prime_ninetyNineCS_14143645819, prime_ninetyNineCS_10335976687219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798402 : Nat.totient 117044421526179420083624798402 = 52473215130043077497017343520 := by
  rw [← show ((([(2, 1), (11, 1), (73, 1), (72879465458393163190301867, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_11, prime_ninetyNineCS_73, prime_ninetyNineCS_72879465458393163190301867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798403 : Nat.totient 117044421526179420083624798403 = 77637589473283650781807404096 := by
  rw [← show ((([(3, 1), (227, 1), (1609, 1), (106818767711888085542707, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_227, prime_ninetyNineCS_1609, prime_ninetyNineCS_106818767711888085542707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798404 : Nat.totient 117044421526179420083624798404 = 50161894939791180035839199304 := by
  rw [← show ((([(2, 2), (7, 1), (4180157911649265002986599943, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_7, prime_ninetyNineCS_4180157911649265002986599943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798405 : Nat.totient 117044421526179420083624798405 = 93462458593917762432765086400 := by
  rw [← show ((([(5, 1), (541, 1), (43269656756443408533687541, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_5, prime_ninetyNineCS_541, prime_ninetyNineCS_43269656756443408533687541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798406 : Nat.totient 117044421526179420083624798406 = 38898980806160405612324966400 := by
  rw [← show ((([(2, 1), (3, 3), (337, 1), (1377469, 1), (1430713, 1), (3263568267301, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_337, prime_ninetyNineCS_1377469, prime_ninetyNineCS_1430713, prime_ninetyNineCS_3263568267301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798407 : Nat.totient 117044421526179420083624798407 = 113008063822502164053765744864 := by
  rw [← show ((([(29, 1), (329309, 1), (12256010419956628103887, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_29, prime_ninetyNineCS_329309, prime_ninetyNineCS_12256010419956628103887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798408 : Nat.totient 117044421526179420083624798408 = 54299646753439027025775083520 := by
  rw [← show ((([(2, 3), (17, 1), (71, 1), (13297, 1), (239963, 1), (3798879437689613, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_17, prime_ninetyNineCS_71, prime_ninetyNineCS_13297, prime_ninetyNineCS_239963, prime_ninetyNineCS_3798879437689613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798409 : Nat.totient 117044421526179420083624798409 = 78009096403464531559400486208 := by
  rw [← show ((([(3, 1), (3803, 1), (2129499557, 1), (4817542840450693, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_3803, prime_ninetyNineCS_2129499557, prime_ninetyNineCS_4817542840450693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798410 : Nat.totient 117044421526179420083624798410 = 46815913486304455287559520448 := by
  rw [← show ((([(2, 1), (5, 1), (25237, 1), (463781041828186472574493, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_5, prime_ninetyNineCS_25237, prime_ninetyNineCS_463781041828186472574493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798411 : Nat.totient 117044421526179420083624798411 = 100110072066041155643239014720 := by
  rw [← show ((([(7, 2), (479, 1), (24943, 1), (385261, 1), (518937902133367, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_7, prime_ninetyNineCS_479, prime_ninetyNineCS_24943, prime_ninetyNineCS_385261, prime_ninetyNineCS_518937902133367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798412 : Nat.totient 117044421526179420083624798412 = 37756255652647657179783840000 := by
  rw [← show ((([(2, 2), (3, 1), (31, 1), (4035601, 1), (77964977642002133471, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_31, prime_ninetyNineCS_4035601, prime_ninetyNineCS_77964977642002133471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798413 : Nat.totient 117044421526179420083624798413 = 98219094987003709161083746800 := by
  rw [← show ((([(11, 1), (13, 1), (818492458225030909675697891, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_11, prime_ninetyNineCS_13, prime_ninetyNineCS_818492458225030909675697891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798414 : Nat.totient 117044421526179420083624798414 = 56940529391114312473114766760 := by
  rw [← show ((([(2, 1), (37, 1), (1581681371975397568697632411, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_37, prime_ninetyNineCS_1581681371975397568697632411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798415 : Nat.totient 117044421526179420083624798415 = 62423691458772597917303116224 := by
  rw [← show ((([(3, 2), (5, 1), (2856079549, 1), (910684419114619463, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_5, prime_ninetyNineCS_2856079549, prime_ninetyNineCS_910684419114619463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798416 : Nat.totient 117044421526179420083624798416 = 57764705821874982200485634432 := by
  rw [← show ((([(2, 4), (83, 1), (1103, 1), (50033843627, 1), (1597030701587, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_83, prime_ninetyNineCS_1103, prime_ninetyNineCS_50033843627, prime_ninetyNineCS_1597030701587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798417 : Nat.totient 117044421526179420083624798417 = 116709050572225735775720367744 := by
  rw [← show ((([(349, 1), (983764777, 1), (340905512333224829, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_349, prime_ninetyNineCS_983764777, prime_ninetyNineCS_340905512333224829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798418 : Nat.totient 117044421526179420083624798418 = 31987292650145574634475153472 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (23, 1), (11963327, 1), (10127951650833345149, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_7, prime_ninetyNineCS_23, prime_ninetyNineCS_11963327, prime_ninetyNineCS_10127951650833345149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798419 : Nat.totient 117044421526179420083624798419 = 117044420281845367090963298896 := by
  rw [← show ((([(94061897, 1), (1244334052992567437627, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_94061897, prime_ninetyNineCS_1244334052992567437627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798420 : Nat.totient 117044421526179420083624798420 = 44353675525710096031689397152 := by
  rw [← show ((([(2, 2), (5, 1), (19, 1), (308011635595209000220065259, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_5, prime_ninetyNineCS_19, prime_ninetyNineCS_308011635595209000220065259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798421 : Nat.totient 117044421526179420083624798421 = 78029614305774814765060553232 := by
  rw [← show ((([(3, 1), (1733549749, 1), (22505732643611106443, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_1733549749, prime_ninetyNineCS_22505732643611106443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798422 : Nat.totient 117044421526179420083624798422 = 57864476966391818937087244800 := by
  rw [← show ((([(2, 1), (89, 1), (328781, 1), (11883769, 1), (168294453805991, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_89, prime_ninetyNineCS_328781, prime_ninetyNineCS_11883769, prime_ninetyNineCS_168294453805991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798423 : Nat.totient 117044421526179420083624798423 = 117041958832941341109145326048 := by
  rw [← show ((([(47527, 1), (2462693238078974479424849, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_47527, prime_ninetyNineCS_2462693238078974479424849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798424 : Nat.totient 117044421526179420083624798424 = 35468006517563368499867413440 := by
  rw [← show ((([(2, 3), (3, 2), (11, 1), (6423847483, 1), (23005427962594859, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_11, prime_ninetyNineCS_6423847483, prime_ninetyNineCS_23005427962594859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798425 : Nat.totient 117044421526179420083624798425 = 72910764334237916221470720000 := by
  rw [← show ((([(5, 2), (7, 1), (17, 1), (43, 1), (101, 1), (557, 1), (8291, 1), (1961606129059303, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_5, prime_ninetyNineCS_7, prime_ninetyNineCS_17, prime_ninetyNineCS_43, prime_ninetyNineCS_101, prime_ninetyNineCS_557, prime_ninetyNineCS_8291, prime_ninetyNineCS_1961606129059303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798426 : Nat.totient 117044421526179420083624798426 = 53001247481114957976654935232 := by
  rw [← show ((([(2, 1), (13, 1), (53, 2), (21746173307, 1), (73695808461227, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_13, prime_ninetyNineCS_53, prime_ninetyNineCS_21746173307, prime_ninetyNineCS_73695808461227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798427 : Nat.totient 117044421526179420083624798427 = 77031252657921097859170708224 := by
  rw [← show ((([(3, 1), (79, 1), (8377, 1), (53267, 1), (37488523, 1), (29522782703, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_79, prime_ninetyNineCS_8377, prime_ninetyNineCS_53267, prime_ninetyNineCS_37488523, prime_ninetyNineCS_29522782703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798428 : Nat.totient 117044421526179420083624798428 = 58471091251323015109148688384 := by
  rw [← show ((([(2, 2), (2113, 1), (3019, 1), (14449, 1), (76067083, 1), (4173434143, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_2113, prime_ninetyNineCS_3019, prime_ninetyNineCS_14449, prime_ninetyNineCS_76067083, prime_ninetyNineCS_4173434143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798429 : Nat.totient 117044421526179420083624798429 = 117044419251244934688087020700 := by
  rw [← show ((([(51449579, 1), (2274934485395486328151, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_51449579, prime_ninetyNineCS_2274934485395486328151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798430 : Nat.totient 117044421526179420083624798430 = 31211845739689881772107609600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (49968546521, 1), (78078731305495561, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_5, prime_ninetyNineCS_49968546521, prime_ninetyNineCS_78078731305495561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798431 : Nat.totient 117044421526179420083624798431 = 117044421526179420083624798430 := by
  rw [← show ((([(117044421526179420083624798431, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_117044421526179420083624798431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798432 : Nat.totient 117044421526179420083624798432 = 50161894939791180035839199232 := by
  rw [← show ((([(2, 5), (7, 1), (522519738956158125373324993, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_7, prime_ninetyNineCS_522519738956158125373324993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798433 : Nat.totient 117044421526179420083624798433 = 78029583819554960802419694840 := by
  rw [← show ((([(3, 4), (2555731, 1), (565393172578762817803, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_2555731, prime_ninetyNineCS_565393172578762817803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798434 : Nat.totient 117044421526179420083624798434 = 58505301716350880307619442160 := by
  rw [← show ((([(2, 1), (3461, 1), (16909046738829734192953597, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3461, prime_ninetyNineCS_16909046738829734192953597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798435 : Nat.totient 117044421526179420083624798435 = 84559439813883476502183552000 := by
  rw [← show ((([(5, 1), (11, 2), (151, 1), (2084903, 1), (15728017, 1), (39071364047, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_5, prime_ninetyNineCS_11, prime_ninetyNineCS_151, prime_ninetyNineCS_2084903, prime_ninetyNineCS_15728017, prime_ninetyNineCS_39071364047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798436 : Nat.totient 117044421526179420083624798436 = 37303732527196242954458941056 := by
  rw [← show ((([(2, 2), (3, 1), (29, 1), (103, 1), (2769443, 1), (1179076055475927283, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_29, prime_ninetyNineCS_103, prime_ninetyNineCS_2769443, prime_ninetyNineCS_1179076055475927283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798437 : Nat.totient 117044421526179420083624798437 = 117040876635823556072933548800 := by
  rw [← show ((([(33211, 1), (5902649, 1), (152969081, 1), (3903176143, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_33211, prime_ninetyNineCS_5902649, prime_ninetyNineCS_152969081, prime_ninetyNineCS_3903176143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798438 : Nat.totient 117044421526179420083624798438 = 58517956767977178987800477896 := by
  rw [← show ((([(2, 1), (13757, 1), (4253995112531054011907567, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_13757, prime_ninetyNineCS_4253995112531054011907567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798439 : Nat.totient 117044421526179420083624798439 = 57061813226064732025788718080 := by
  rw [← show ((([(3, 1), (7, 1), (13, 1), (19, 1), (41, 1), (12251719, 1), (44921431500426643, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_7, prime_ninetyNineCS_13, prime_ninetyNineCS_19, prime_ninetyNineCS_41, prime_ninetyNineCS_12251719, prime_ninetyNineCS_44921431500426643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798440 : Nat.totient 117044421526179420083624798440 = 46817768610471768033449919360 := by
  rw [← show ((([(2, 3), (5, 1), (2926110538154485502090619961, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_5, prime_ninetyNineCS_2926110538154485502090619961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798441 : Nat.totient 117044421526179420083624798441 = 111920802752647717142507271936 := by
  rw [← show ((([(23, 1), (4507, 1), (11317, 1), (8767068397, 1), (11380192669, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_23, prime_ninetyNineCS_4507, prime_ninetyNineCS_11317, prime_ninetyNineCS_8767068397, prime_ninetyNineCS_11380192669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798442 : Nat.totient 117044421526179420083624798442 = 36171761525210847997748833920 := by
  rw [← show ((([(2, 1), (3, 2), (17, 1), (67, 1), (5708927008398176767321471, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_17, prime_ninetyNineCS_67, prime_ninetyNineCS_5708927008398176767321471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798443 : Nat.totient 117044421526179420083624798443 = 113267151914067811251920845440 := by
  rw [← show ((([(31, 1), (82193, 1), (427379, 1), (107483305702924999, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_31, prime_ninetyNineCS_82193, prime_ninetyNineCS_427379, prime_ninetyNineCS_107483305702924999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798444 : Nat.totient 117044421526179420083624798444 = 58490160117920630032956422400 := by
  rw [← show ((([(2, 2), (2693, 1), (5669, 1), (1240839983, 1), (1544657291101, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_2693, prime_ninetyNineCS_5669, prime_ninetyNineCS_1240839983, prime_ninetyNineCS_1544657291101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798445 : Nat.totient 117044421526179420083624798445 = 62185335668228046945721114944 := by
  rw [← show ((([(3, 1), (5, 1), (283, 1), (3499, 1), (7880051983634524559339, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_5, prime_ninetyNineCS_283, prime_ninetyNineCS_3499, prime_ninetyNineCS_7880051983634524559339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798446 : Nat.totient 117044421526179420083624798446 = 44567214864235809286275072000 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (47, 1), (1301, 1), (1489, 1), (24904889, 1), (335178023777, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_7, prime_ninetyNineCS_11, prime_ninetyNineCS_47, prime_ninetyNineCS_1301, prime_ninetyNineCS_1489, prime_ninetyNineCS_24904889, prime_ninetyNineCS_335178023777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798447 : Nat.totient 117044421526179420083624798447 = 117044421387680918172338267040 := by
  rw [← show ((([(845095217, 1), (138498501910441436191, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_845095217, prime_ninetyNineCS_138498501910441436191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798448 : Nat.totient 117044421526179420083624798448 = 39014665484805140740325452800 := by
  rw [← show ((([(2, 4), (3, 1), (275453, 1), (752072917, 1), (11770692816901, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_275453, prime_ninetyNineCS_752072917, prime_ninetyNineCS_11770692816901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798449 : Nat.totient 117044421526179420083624798449 = 116939259115099290451685376000 := by
  rw [← show ((([(1217, 1), (13469, 1), (647201, 1), (940031, 1), (11736630523, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_1217, prime_ninetyNineCS_13469, prime_ninetyNineCS_647201, prime_ninetyNineCS_940031, prime_ninetyNineCS_11736630523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798450 : Nat.totient 117044421526179420083624798450 = 46575184681225698804491550720 := by
  rw [← show ((([(2, 1), (5, 2), (193, 1), (9668369, 1), (1254498623146035857, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_5, prime_ninetyNineCS_193, prime_ninetyNineCS_9668369, prime_ninetyNineCS_1254498623146035857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798451 : Nat.totient 117044421526179420083624798451 = 75775536066317782958063760960 := by
  rw [← show ((([(3, 2), (37, 1), (523, 1), (12810799, 1), (52460035477425011, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_37, prime_ninetyNineCS_523, prime_ninetyNineCS_12810799, prime_ninetyNineCS_52460035477425011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798452 : Nat.totient 117044421526179420083624798452 = 53791498093461364740668976000 := by
  rw [← show ((([(2, 2), (13, 1), (271, 1), (2851, 1), (4987, 1), (584173025748480463, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_13, prime_ninetyNineCS_271, prime_ninetyNineCS_2851, prime_ninetyNineCS_4987, prime_ninetyNineCS_584173025748480463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798453 : Nat.totient 117044421526179420083624798453 = 100323789871354956196337508480 := by
  rw [← show ((([(7, 1), (12193857539, 1), (1371233967029624161, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_7, prime_ninetyNineCS_12193857539, prime_ninetyNineCS_1371233967029624161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798454 : Nat.totient 117044421526179420083624798454 = 39014807146758107928574947240 := by
  rw [← show ((([(2, 1), (3, 1), (1362485191, 1), (14317516048287507599, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_1362485191, prime_ninetyNineCS_14317516048287507599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798455 : Nat.totient 117044421526179420083624798455 = 93635522107884505928337900160 := by
  rw [← show ((([(5, 1), (6203573, 1), (4894699571, 1), (770926150277, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_5, prime_ninetyNineCS_6203573, prime_ninetyNineCS_4894699571, prime_ninetyNineCS_770926150277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798456 : Nat.totient 117044421526179420083624798456 = 58490521254147142699143276672 := by
  rw [← show ((([(2, 3), (1847, 1), (13970287, 1), (199600837, 1), (2840705099, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_1847, prime_ninetyNineCS_13970287, prime_ninetyNineCS_199600837, prime_ninetyNineCS_2840705099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798457 : Nat.totient 117044421526179420083624798457 = 70464160088632807239948791040 := by
  rw [← show ((([(3, 1), (11, 1), (157, 1), (3583, 1), (196727, 1), (67127519, 1), (477447643, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_11, prime_ninetyNineCS_157, prime_ninetyNineCS_3583, prime_ninetyNineCS_196727, prime_ninetyNineCS_67127519, prime_ninetyNineCS_477447643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798458 : Nat.totient 117044421526179420083624798458 = 53993029687166495802872219184 := by
  rw [← show ((([(2, 1), (19, 1), (59, 1), (107, 1), (487900579114856645366807, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_19, prime_ninetyNineCS_59, prime_ninetyNineCS_107, prime_ninetyNineCS_487900579114856645366807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798459 : Nat.totient 117044421526179420083624798459 = 108307863319662336068322163200 := by
  rw [← show ((([(17, 1), (61, 1), (2371, 1), (47603667070878312266317, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_17, prime_ninetyNineCS_61, prime_ninetyNineCS_2371, prime_ninetyNineCS_47603667070878312266317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798460 : Nat.totient 117044421526179420083624798460 = 26753009315965182052767812736 := by
  rw [← show ((([(2, 2), (3, 3), (5, 1), (7, 2), (20289103, 1), (218020852156686167, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_5, prime_ninetyNineCS_7, prime_ninetyNineCS_20289103, prime_ninetyNineCS_218020852156686167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798461 : Nat.totient 117044421526179420083624798461 = 117044366234663142292493265408 := by
  rw [← show ((([(4119937, 1), (4353967, 1), (6524917297242259, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_4119937, prime_ninetyNineCS_4353967, prime_ninetyNineCS_6524917297242259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798462 : Nat.totient 117044421526179420083624798462 = 58163178793899115151050603392 := by
  rw [← show ((([(2, 1), (163, 1), (44100709189, 1), (8141183542718833, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_163, prime_ninetyNineCS_44100709189, prime_ninetyNineCS_8141183542718833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798463 : Nat.totient 117044421526179420083624798463 = 77328811972303030518129036000 := by
  rw [← show ((([(3, 1), (139, 1), (859, 1), (1571, 1), (207991370074170734351, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_139, prime_ninetyNineCS_859, prime_ninetyNineCS_1571, prime_ninetyNineCS_207991370074170734351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798464 : Nat.totient 117044421526179420083624798464 = 55654191775155461744436224000 := by
  rw [← show ((([(2, 8), (23, 1), (173, 1), (13458461, 1), (8537710308260951, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_23, prime_ninetyNineCS_173, prime_ninetyNineCS_13458461, prime_ninetyNineCS_8537710308260951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798465 : Nat.totient 117044421526179420083624798465 = 83452362085509358404451844352 := by
  rw [← show ((([(5, 1), (13, 1), (29, 1), (62092531313623034527121909, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_5, prime_ninetyNineCS_13, prime_ninetyNineCS_29, prime_ninetyNineCS_62092531313623034527121909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798466 : Nat.totient 117044421526179420083624798466 = 38635380047554293011820926400 := by
  rw [← show ((([(2, 1), (3, 1), (131, 1), (487, 1), (18371, 1), (16644333730688624053, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_131, prime_ninetyNineCS_487, prime_ninetyNineCS_18371, prime_ninetyNineCS_16644333730688624053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798467 : Nat.totient 117044421526179420083624798467 = 99557466730198816838400000000 := by
  rw [← show ((([(7, 1), (241, 1), (401, 1), (991, 1), (299401, 1), (583128628247651, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_7, prime_ninetyNineCS_241, prime_ninetyNineCS_401, prime_ninetyNineCS_991, prime_ninetyNineCS_299401, prime_ninetyNineCS_583128628247651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798468 : Nat.totient 117044421526179420083624798468 = 51663696929310825983060398080 := by
  rw [← show ((([(2, 2), (11, 1), (43, 1), (223, 1), (997, 1), (5477, 1), (7703, 1), (6595184164489, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_11, prime_ninetyNineCS_43, prime_ninetyNineCS_223, prime_ninetyNineCS_997, prime_ninetyNineCS_5477, prime_ninetyNineCS_7703, prime_ninetyNineCS_6595184164489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798469 : Nat.totient 117044421526179420083624798469 = 78029599350381374548386817920 := by
  rw [← show ((([(3, 2), (5800019, 1), (50437169, 1), (44455765394431, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_5800019, prime_ninetyNineCS_50437169, prime_ninetyNineCS_44455765394431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798470 : Nat.totient 117044421526179420083624798470 = 46616612098807108651852366848 := by
  rw [← show ((([(2, 1), (5, 1), (233, 1), (210097, 1), (239097451688377947647, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_5, prime_ninetyNineCS_233, prime_ninetyNineCS_210097, prime_ninetyNineCS_239097451688377947647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798471 : Nat.totient 117044421526179420083624798471 = 116919506906535361854973867200 := by
  rw [← show ((([(937, 1), (189841133, 1), (657992300136899851, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_937, prime_ninetyNineCS_189841133, prime_ninetyNineCS_657992300136899851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798472 : Nat.totient 117044421526179420083624798472 = 38901635500517649206566571520 := by
  rw [← show ((([(2, 3), (3, 1), (347, 1), (53113, 1), (8408143, 1), (31470894077911, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_347, prime_ninetyNineCS_53113, prime_ninetyNineCS_8408143, prime_ninetyNineCS_31470894077911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798473 : Nat.totient 117044421526179420083624798473 = 117044421526133925791600320128 := by
  rw [← show ((([(2572873123057, 1), (45491719151355289, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2572873123057, prime_ninetyNineCS_45491719151355289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798474 : Nat.totient 117044421526179420083624798474 = 48313704039242384073656430000 := by
  rw [← show ((([(2, 1), (7, 1), (31, 1), (211, 1), (1278140318498475769144351, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_7, prime_ninetyNineCS_31, prime_ninetyNineCS_211, prime_ninetyNineCS_1278140318498475769144351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798475 : Nat.totient 117044421526179420083624798475 = 61558874431654205933521920000 := by
  rw [← show ((([(3, 1), (5, 2), (73, 1), (6361, 1), (4240079, 1), (25305101, 1), (31322699, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_5, prime_ninetyNineCS_73, prime_ninetyNineCS_6361, prime_ninetyNineCS_4240079, prime_ninetyNineCS_25305101, prime_ninetyNineCS_31322699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798476 : Nat.totient 117044421526179420083624798476 = 55079727775310149095783932928 := by
  rw [← show ((([(2, 2), (17, 2), (32108167603, 1), (3153387662666257, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_17, prime_ninetyNineCS_32108167603, prime_ninetyNineCS_3153387662666257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798477 : Nat.totient 117044421526179420083624798477 = 110583294692295938847505920000 := by
  rw [← show ((([(19, 1), (601, 1), (977, 1), (35801, 1), (293044061755608479, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_19, prime_ninetyNineCS_601, prime_ninetyNineCS_977, prime_ninetyNineCS_35801, prime_ninetyNineCS_293044061755608479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798478 : Nat.totient 117044421526179420083624798478 = 35913351537494949552121403712 := by
  rw [← show ((([(2, 1), (3, 2), (13, 1), (359, 1), (1393286450089034355684413, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_13, prime_ninetyNineCS_359, prime_ninetyNineCS_1393286450089034355684413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798479 : Nat.totient 117044421526179420083624798479 = 102817179529155847842973286400 := by
  rw [← show ((([(11, 1), (53, 1), (71, 1), (947, 1), (903037, 1), (2289193, 1), (1444394689, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_11, prime_ninetyNineCS_53, prime_ninetyNineCS_71, prime_ninetyNineCS_947, prime_ninetyNineCS_903037, prime_ninetyNineCS_2289193, prime_ninetyNineCS_1444394689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798480 : Nat.totient 117044421526179420083624798480 = 45256827119543082994965995520 := by
  rw [← show ((([(2, 4), (5, 1), (41, 1), (109, 1), (327378668399472533239049, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_5, prime_ninetyNineCS_41, prime_ninetyNineCS_109, prime_ninetyNineCS_327378668399472533239049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798481 : Nat.totient 117044421526179420083624798481 = 66591213999995452731430372416 := by
  rw [← show ((([(3, 1), (7, 1), (239, 1), (5807, 1), (4015888977016643456557, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_7, prime_ninetyNineCS_239, prime_ninetyNineCS_5807, prime_ninetyNineCS_4015888977016643456557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798482 : Nat.totient 117044421526179420083624798482 = 57918888204027277471704135168 := by
  rw [← show ((([(2, 1), (97, 1), (76910429, 1), (1792284803, 1), (4376800319, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_97, prime_ninetyNineCS_76910429, prime_ninetyNineCS_1792284803, prime_ninetyNineCS_4376800319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798483 : Nat.totient 117044421526179420083624798483 = 117044421526179420083624798482 := by
  rw [← show ((([(117044421526179420083624798483, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_117044421526179420083624798483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798484 : Nat.totient 117044421526179420083624798484 = 39014807175393140027874932824 := by
  rw [← show ((([(2, 2), (3, 1), (9753701793848285006968733207, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_9753701793848285006968733207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798485 : Nat.totient 117044421526179420083624798485 = 93618038520942969257632728000 := by
  rw [← show ((([(5, 1), (5351, 1), (77387997307, 1), (56529111096421, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_5, prime_ninetyNineCS_5351, prime_ninetyNineCS_77387997307, prime_ninetyNineCS_56529111096421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798486 : Nat.totient 117044421526179420083624798486 = 58463424454439687805839676960 := by
  rw [← show ((([(2, 1), (1171, 1), (6637, 1), (7529948591010917889709, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_1171, prime_ninetyNineCS_6637, prime_ninetyNineCS_7529948591010917889709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798487 : Nat.totient 117044421526179420083624798487 = 74592302816486136789167471136 := by
  rw [← show ((([(3, 3), (23, 1), (1669, 1), (112928297992645484807863, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_23, prime_ninetyNineCS_1669, prime_ninetyNineCS_112928297992645484807863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798488 : Nat.totient 117044421526179420083624798488 = 48798421801165938892831948800 := by
  rw [← show ((([(2, 3), (7, 1), (37, 1), (6301, 1), (104482753, 1), (85803871067093, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_7, prime_ninetyNineCS_37, prime_ninetyNineCS_6301, prime_ninetyNineCS_104482753, prime_ninetyNineCS_85803871067093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798489 : Nat.totient 117044421526179420083624798489 = 116820499365728595909945138960 := by
  rw [← show ((([(691, 1), (2143, 1), (79040649647308215205853, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_691, prime_ninetyNineCS_2143, prime_ninetyNineCS_79040649647308215205853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798490 : Nat.totient 117044421526179420083624798490 = 28343258780247685800112641600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (11, 1), (911, 1), (389330477750655024726823, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_5, prime_ninetyNineCS_11, prime_ninetyNineCS_911, prime_ninetyNineCS_389330477750655024726823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798491 : Nat.totient 117044421526179420083624798491 = 108036703620593570205070571520 := by
  rw [← show ((([(13, 2), (25121, 1), (2640850507, 1), (10439585944937, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_13, prime_ninetyNineCS_25121, prime_ninetyNineCS_2640850507, prime_ninetyNineCS_10439585944937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798492 : Nat.totient 117044421526179420083624798492 = 58522210546232941630850919120 := by
  rw [← show ((([(2, 2), (269865733, 1), (108428384205210874331, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_269865733, prime_ninetyNineCS_108428384205210874331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798493 : Nat.totient 117044421526179420083624798493 = 71597374916690882902870720512 := by
  rw [← show ((([(3, 1), (17, 1), (47, 1), (257, 1), (1824073, 1), (104161529215238329, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_17, prime_ninetyNineCS_47, prime_ninetyNineCS_257, prime_ninetyNineCS_1824073, prime_ninetyNineCS_104161529215238329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798494 : Nat.totient 117044421526179420083624798494 = 56123526751100715769736813184 := by
  rw [← show ((([(2, 1), (29, 1), (149, 1), (38603, 1), (350845088141730581869, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_29, prime_ninetyNineCS_149, prime_ninetyNineCS_38603, prime_ninetyNineCS_350845088141730581869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798495 : Nat.totient 117044421526179420083624798495 = 79989963242206272482489794560 := by
  rw [← show ((([(5, 1), (7, 1), (457, 1), (857, 1), (86231221, 1), (99019588599233, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_5, prime_ninetyNineCS_7, prime_ninetyNineCS_457, prime_ninetyNineCS_857, prime_ninetyNineCS_86231221, prime_ninetyNineCS_99019588599233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798496 : Nat.totient 117044421526179420083624798496 = 36839323833009074095753267200 := by
  rw [← show ((([(2, 5), (3, 2), (19, 1), (331, 1), (3541, 1), (18249489080724596333, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_3, prime_ninetyNineCS_19, prime_ninetyNineCS_331, prime_ninetyNineCS_3541, prime_ninetyNineCS_18249489080724596333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798497 : Nat.totient 117044421526179420083624798497 = 117038081434046903977302144000 := by
  rw [← show ((([(18461, 1), (111984858901, 1), (56615609891777, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_18461, prime_ninetyNineCS_111984858901, prime_ninetyNineCS_56615609891777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798498 : Nat.totient 117044421526179420083624798498 = 58495113911608089118047797760 := by
  rw [← show ((([(2, 1), (2161, 1), (3766073, 1), (244951459, 1), (29356021187, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_2161, prime_ninetyNineCS_3766073, prime_ninetyNineCS_244951459, prime_ninetyNineCS_29356021187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798499 : Nat.totient 117044421526179420083624798499 = 77070259645500891713847338240 := by
  rw [← show ((([(3, 1), (83, 1), (4007, 1), (473283353, 1), (247862485804181, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_3, prime_ninetyNineCS_83, prime_ninetyNineCS_4007, prime_ninetyNineCS_473283353, prime_ninetyNineCS_247862485804181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798500 : Nat.totient 117044421526179420083624798500 = 46817768610471768033449919200 := by
  rw [← show ((([(2, 2), (5, 3), (234088843052358840167249597, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_2, prime_ninetyNineCS_5, prime_ninetyNineCS_234088843052358840167249597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyNineCS_117044421526179420083624798501 : Nat.totient 117044421526179420083624798501 = 105419814415771899032577772800 := by
  rw [← show ((([(11, 1), (113, 1), (2477, 1), (38014876534651186761691, 1)] : List FactorBlock).map factorBlockValue).prod) = 117044421526179420083624798501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyNineCS_11, prime_ninetyNineCS_113, prime_ninetyNineCS_2477, prime_ninetyNineCS_38014876534651186761691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NinetyNineCS : certifiedKill 1 117044421526179420083624798399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_ninetyNineCS_117044421526179420083624798400, phi_ninetyNineCS_117044421526179420083624798401, phi_ninetyNineCS_117044421526179420083624798402,
    phi_ninetyNineCS_117044421526179420083624798403, phi_ninetyNineCS_117044421526179420083624798404, phi_ninetyNineCS_117044421526179420083624798405,
    phi_ninetyNineCS_117044421526179420083624798406, phi_ninetyNineCS_117044421526179420083624798407, phi_ninetyNineCS_117044421526179420083624798408,
    phi_ninetyNineCS_117044421526179420083624798409, phi_ninetyNineCS_117044421526179420083624798410, phi_ninetyNineCS_117044421526179420083624798411,
    phi_ninetyNineCS_117044421526179420083624798412, phi_ninetyNineCS_117044421526179420083624798413, phi_ninetyNineCS_117044421526179420083624798414,
    phi_ninetyNineCS_117044421526179420083624798415, phi_ninetyNineCS_117044421526179420083624798416, phi_ninetyNineCS_117044421526179420083624798417,
    phi_ninetyNineCS_117044421526179420083624798418, phi_ninetyNineCS_117044421526179420083624798419, phi_ninetyNineCS_117044421526179420083624798420,
    phi_ninetyNineCS_117044421526179420083624798421, phi_ninetyNineCS_117044421526179420083624798422, phi_ninetyNineCS_117044421526179420083624798423,
    phi_ninetyNineCS_117044421526179420083624798424, phi_ninetyNineCS_117044421526179420083624798425, phi_ninetyNineCS_117044421526179420083624798426,
    phi_ninetyNineCS_117044421526179420083624798427, phi_ninetyNineCS_117044421526179420083624798428, phi_ninetyNineCS_117044421526179420083624798429,
    phi_ninetyNineCS_117044421526179420083624798430, phi_ninetyNineCS_117044421526179420083624798431, phi_ninetyNineCS_117044421526179420083624798432,
    phi_ninetyNineCS_117044421526179420083624798433, phi_ninetyNineCS_117044421526179420083624798434, phi_ninetyNineCS_117044421526179420083624798435,
    phi_ninetyNineCS_117044421526179420083624798436, phi_ninetyNineCS_117044421526179420083624798437, phi_ninetyNineCS_117044421526179420083624798438,
    phi_ninetyNineCS_117044421526179420083624798439, phi_ninetyNineCS_117044421526179420083624798440, phi_ninetyNineCS_117044421526179420083624798441,
    phi_ninetyNineCS_117044421526179420083624798442, phi_ninetyNineCS_117044421526179420083624798443, phi_ninetyNineCS_117044421526179420083624798444,
    phi_ninetyNineCS_117044421526179420083624798445, phi_ninetyNineCS_117044421526179420083624798446, phi_ninetyNineCS_117044421526179420083624798447,
    phi_ninetyNineCS_117044421526179420083624798448, phi_ninetyNineCS_117044421526179420083624798449, phi_ninetyNineCS_117044421526179420083624798450,
    phi_ninetyNineCS_117044421526179420083624798451, phi_ninetyNineCS_117044421526179420083624798452, phi_ninetyNineCS_117044421526179420083624798453,
    phi_ninetyNineCS_117044421526179420083624798454, phi_ninetyNineCS_117044421526179420083624798455, phi_ninetyNineCS_117044421526179420083624798456,
    phi_ninetyNineCS_117044421526179420083624798457, phi_ninetyNineCS_117044421526179420083624798458, phi_ninetyNineCS_117044421526179420083624798459,
    phi_ninetyNineCS_117044421526179420083624798460, phi_ninetyNineCS_117044421526179420083624798461, phi_ninetyNineCS_117044421526179420083624798462,
    phi_ninetyNineCS_117044421526179420083624798463, phi_ninetyNineCS_117044421526179420083624798464, phi_ninetyNineCS_117044421526179420083624798465,
    phi_ninetyNineCS_117044421526179420083624798466, phi_ninetyNineCS_117044421526179420083624798467, phi_ninetyNineCS_117044421526179420083624798468,
    phi_ninetyNineCS_117044421526179420083624798469, phi_ninetyNineCS_117044421526179420083624798470, phi_ninetyNineCS_117044421526179420083624798471,
    phi_ninetyNineCS_117044421526179420083624798472, phi_ninetyNineCS_117044421526179420083624798473, phi_ninetyNineCS_117044421526179420083624798474,
    phi_ninetyNineCS_117044421526179420083624798475, phi_ninetyNineCS_117044421526179420083624798476, phi_ninetyNineCS_117044421526179420083624798477,
    phi_ninetyNineCS_117044421526179420083624798478, phi_ninetyNineCS_117044421526179420083624798479, phi_ninetyNineCS_117044421526179420083624798480,
    phi_ninetyNineCS_117044421526179420083624798481, phi_ninetyNineCS_117044421526179420083624798482, phi_ninetyNineCS_117044421526179420083624798483,
    phi_ninetyNineCS_117044421526179420083624798484, phi_ninetyNineCS_117044421526179420083624798485, phi_ninetyNineCS_117044421526179420083624798486,
    phi_ninetyNineCS_117044421526179420083624798487, phi_ninetyNineCS_117044421526179420083624798488, phi_ninetyNineCS_117044421526179420083624798489,
    phi_ninetyNineCS_117044421526179420083624798490, phi_ninetyNineCS_117044421526179420083624798491, phi_ninetyNineCS_117044421526179420083624798492,
    phi_ninetyNineCS_117044421526179420083624798493, phi_ninetyNineCS_117044421526179420083624798494, phi_ninetyNineCS_117044421526179420083624798495,
    phi_ninetyNineCS_117044421526179420083624798496, phi_ninetyNineCS_117044421526179420083624798497, phi_ninetyNineCS_117044421526179420083624798498,
    phi_ninetyNineCS_117044421526179420083624798499, phi_ninetyNineCS_117044421526179420083624798500, phi_ninetyNineCS_117044421526179420083624798501
    ]

end TotientTailPeriodKiller
end Erdos249257
