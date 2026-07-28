import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def ninetySevenCQFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem ninetySevenCQFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : ninetySevenCQFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [ninetySevenCQFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [ninetySevenCQFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then ninetySevenCQFastPow a n * ninetySevenCQFastPow a n * a else ninetySevenCQFastPow a n * ninetySevenCQFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_ninetySevenCQ_2 : Nat.Prime 2 := by norm_num

private theorem prime_ninetySevenCQ_3 : Nat.Prime 3 := by norm_num

private theorem prime_ninetySevenCQ_5 : Nat.Prime 5 := by norm_num

private theorem prime_ninetySevenCQ_7 : Nat.Prime 7 := by norm_num

private theorem prime_ninetySevenCQ_11 : Nat.Prime 11 := by norm_num

private theorem prime_ninetySevenCQ_13 : Nat.Prime 13 := by norm_num

private theorem prime_ninetySevenCQ_17 : Nat.Prime 17 := by norm_num

private theorem prime_ninetySevenCQ_19 : Nat.Prime 19 := by norm_num

private theorem prime_ninetySevenCQ_23 : Nat.Prime 23 := by norm_num

private theorem prime_ninetySevenCQ_29 : Nat.Prime 29 := by norm_num

private theorem prime_ninetySevenCQ_31 : Nat.Prime 31 := by norm_num

private theorem prime_ninetySevenCQ_37 : Nat.Prime 37 := by norm_num

private theorem prime_ninetySevenCQ_41 : Nat.Prime 41 := by norm_num

private theorem prime_ninetySevenCQ_43 : Nat.Prime 43 := by norm_num

private theorem prime_ninetySevenCQ_47 : Nat.Prime 47 := by norm_num

private theorem prime_ninetySevenCQ_53 : Nat.Prime 53 := by norm_num

private theorem prime_ninetySevenCQ_59 : Nat.Prime 59 := by norm_num

private theorem prime_ninetySevenCQ_61 : Nat.Prime 61 := by norm_num

private theorem prime_ninetySevenCQ_67 : Nat.Prime 67 := by norm_num

private theorem prime_ninetySevenCQ_71 : Nat.Prime 71 := by norm_num

private theorem prime_ninetySevenCQ_73 : Nat.Prime 73 := by norm_num

private theorem prime_ninetySevenCQ_79 : Nat.Prime 79 := by norm_num

private theorem prime_ninetySevenCQ_83 : Nat.Prime 83 := by norm_num

private theorem prime_ninetySevenCQ_89 : Nat.Prime 89 := by norm_num

private theorem prime_ninetySevenCQ_97 : Nat.Prime 97 := by norm_num

private theorem prime_ninetySevenCQ_101 : Nat.Prime 101 := by norm_num

private theorem prime_ninetySevenCQ_103 : Nat.Prime 103 := by norm_num

private theorem prime_ninetySevenCQ_107 : Nat.Prime 107 := by norm_num

private theorem prime_ninetySevenCQ_109 : Nat.Prime 109 := by norm_num

private theorem prime_ninetySevenCQ_113 : Nat.Prime 113 := by norm_num

private theorem prime_ninetySevenCQ_127 : Nat.Prime 127 := by norm_num

private theorem prime_ninetySevenCQ_131 : Nat.Prime 131 := by norm_num

private theorem prime_ninetySevenCQ_137 : Nat.Prime 137 := by norm_num

private theorem prime_ninetySevenCQ_139 : Nat.Prime 139 := by norm_num

private theorem prime_ninetySevenCQ_149 : Nat.Prime 149 := by norm_num

private theorem prime_ninetySevenCQ_151 : Nat.Prime 151 := by norm_num

private theorem prime_ninetySevenCQ_157 : Nat.Prime 157 := by norm_num

private theorem prime_ninetySevenCQ_163 : Nat.Prime 163 := by norm_num

private theorem prime_ninetySevenCQ_167 : Nat.Prime 167 := by norm_num

private theorem prime_ninetySevenCQ_173 : Nat.Prime 173 := by norm_num

private theorem prime_ninetySevenCQ_179 : Nat.Prime 179 := by norm_num

private theorem prime_ninetySevenCQ_181 : Nat.Prime 181 := by norm_num

private theorem prime_ninetySevenCQ_191 : Nat.Prime 191 := by norm_num

private theorem prime_ninetySevenCQ_193 : Nat.Prime 193 := by norm_num

private theorem prime_ninetySevenCQ_199 : Nat.Prime 199 := by norm_num

private theorem prime_ninetySevenCQ_211 : Nat.Prime 211 := by norm_num

private theorem prime_ninetySevenCQ_223 : Nat.Prime 223 := by norm_num

private theorem prime_ninetySevenCQ_227 : Nat.Prime 227 := by norm_num

private theorem prime_ninetySevenCQ_229 : Nat.Prime 229 := by norm_num

private theorem prime_ninetySevenCQ_233 : Nat.Prime 233 := by norm_num

private theorem prime_ninetySevenCQ_239 : Nat.Prime 239 := by norm_num

private theorem prime_ninetySevenCQ_251 : Nat.Prime 251 := by norm_num

private theorem prime_ninetySevenCQ_257 : Nat.Prime 257 := by norm_num

private theorem prime_ninetySevenCQ_269 : Nat.Prime 269 := by norm_num

private theorem prime_ninetySevenCQ_271 : Nat.Prime 271 := by norm_num

private theorem prime_ninetySevenCQ_281 : Nat.Prime 281 := by norm_num

private theorem prime_ninetySevenCQ_293 : Nat.Prime 293 := by norm_num

private theorem prime_ninetySevenCQ_307 : Nat.Prime 307 := by norm_num

private theorem prime_ninetySevenCQ_311 : Nat.Prime 311 := by norm_num

private theorem prime_ninetySevenCQ_313 : Nat.Prime 313 := by norm_num

private theorem prime_ninetySevenCQ_317 : Nat.Prime 317 := by norm_num

private theorem prime_ninetySevenCQ_331 : Nat.Prime 331 := by norm_num

private theorem prime_ninetySevenCQ_347 : Nat.Prime 347 := by norm_num

private theorem prime_ninetySevenCQ_367 : Nat.Prime 367 := by norm_num

private theorem prime_ninetySevenCQ_383 : Nat.Prime 383 := by norm_num

private theorem prime_ninetySevenCQ_397 : Nat.Prime 397 := by norm_num

private theorem prime_ninetySevenCQ_409 : Nat.Prime 409 := by norm_num

private theorem prime_ninetySevenCQ_419 : Nat.Prime 419 := by norm_num

private theorem prime_ninetySevenCQ_431 : Nat.Prime 431 := by norm_num

private theorem prime_ninetySevenCQ_433 : Nat.Prime 433 := by norm_num

private theorem prime_ninetySevenCQ_443 : Nat.Prime 443 := by norm_num

private theorem prime_ninetySevenCQ_449 : Nat.Prime 449 := by norm_num

private theorem prime_ninetySevenCQ_457 : Nat.Prime 457 := by norm_num

private theorem prime_ninetySevenCQ_461 : Nat.Prime 461 := by norm_num

private theorem prime_ninetySevenCQ_463 : Nat.Prime 463 := by norm_num

private theorem prime_ninetySevenCQ_467 : Nat.Prime 467 := by norm_num

private theorem prime_ninetySevenCQ_487 : Nat.Prime 487 := by norm_num

private theorem prime_ninetySevenCQ_491 : Nat.Prime 491 := by norm_num

private theorem prime_ninetySevenCQ_509 : Nat.Prime 509 := by norm_num

private theorem prime_ninetySevenCQ_563 : Nat.Prime 563 := by norm_num

private theorem prime_ninetySevenCQ_569 : Nat.Prime 569 := by norm_num

private theorem prime_ninetySevenCQ_571 : Nat.Prime 571 := by norm_num

private theorem prime_ninetySevenCQ_593 : Nat.Prime 593 := by norm_num

private theorem prime_ninetySevenCQ_599 : Nat.Prime 599 := by norm_num

private theorem prime_ninetySevenCQ_607 : Nat.Prime 607 := by norm_num

private theorem prime_ninetySevenCQ_617 : Nat.Prime 617 := by norm_num

private theorem prime_ninetySevenCQ_631 : Nat.Prime 631 := by norm_num

private theorem prime_ninetySevenCQ_641 : Nat.Prime 641 := by norm_num

private theorem prime_ninetySevenCQ_659 : Nat.Prime 659 := by norm_num

private theorem prime_ninetySevenCQ_673 : Nat.Prime 673 := by norm_num

private theorem prime_ninetySevenCQ_683 : Nat.Prime 683 := by norm_num

private theorem prime_ninetySevenCQ_691 : Nat.Prime 691 := by norm_num

private theorem prime_ninetySevenCQ_719 : Nat.Prime 719 := by norm_num

private theorem prime_ninetySevenCQ_739 : Nat.Prime 739 := by norm_num

private theorem prime_ninetySevenCQ_743 : Nat.Prime 743 := by norm_num

private theorem prime_ninetySevenCQ_751 : Nat.Prime 751 := by norm_num

private theorem prime_ninetySevenCQ_769 : Nat.Prime 769 := by norm_num

private theorem prime_ninetySevenCQ_787 : Nat.Prime 787 := by norm_num

private theorem prime_ninetySevenCQ_797 : Nat.Prime 797 := by norm_num

private theorem prime_ninetySevenCQ_811 : Nat.Prime 811 := by norm_num

private theorem prime_ninetySevenCQ_821 : Nat.Prime 821 := by norm_num

private theorem prime_ninetySevenCQ_823 : Nat.Prime 823 := by norm_num

private theorem prime_ninetySevenCQ_853 : Nat.Prime 853 := by norm_num

private theorem prime_ninetySevenCQ_929 : Nat.Prime 929 := by norm_num

private theorem prime_ninetySevenCQ_977 : Nat.Prime 977 := by norm_num

private theorem prime_ninetySevenCQ_991 : Nat.Prime 991 := by norm_num

private theorem prime_ninetySevenCQ_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_ninetySevenCQ_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_ninetySevenCQ_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_ninetySevenCQ_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_ninetySevenCQ_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_ninetySevenCQ_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_ninetySevenCQ_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_ninetySevenCQ_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_ninetySevenCQ_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_ninetySevenCQ_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_ninetySevenCQ_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_ninetySevenCQ_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_ninetySevenCQ_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_ninetySevenCQ_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_ninetySevenCQ_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_ninetySevenCQ_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_ninetySevenCQ_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_ninetySevenCQ_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_ninetySevenCQ_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_ninetySevenCQ_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_ninetySevenCQ_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_ninetySevenCQ_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_ninetySevenCQ_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_ninetySevenCQ_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_ninetySevenCQ_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_ninetySevenCQ_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_ninetySevenCQ_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_ninetySevenCQ_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_ninetySevenCQ_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_ninetySevenCQ_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_ninetySevenCQ_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_ninetySevenCQ_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_ninetySevenCQ_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_ninetySevenCQ_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_ninetySevenCQ_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_ninetySevenCQ_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_ninetySevenCQ_2017 : Nat.Prime 2017 := by norm_num

private theorem prime_ninetySevenCQ_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_ninetySevenCQ_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_ninetySevenCQ_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_ninetySevenCQ_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_ninetySevenCQ_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_ninetySevenCQ_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_ninetySevenCQ_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_ninetySevenCQ_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_ninetySevenCQ_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_ninetySevenCQ_2531 : Nat.Prime 2531 := by norm_num

private theorem prime_ninetySevenCQ_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_ninetySevenCQ_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_ninetySevenCQ_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_ninetySevenCQ_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_ninetySevenCQ_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_ninetySevenCQ_2837 : Nat.Prime 2837 := by norm_num

private theorem prime_ninetySevenCQ_2861 : Nat.Prime 2861 := by norm_num

private theorem prime_ninetySevenCQ_2969 : Nat.Prime 2969 := by norm_num

private theorem prime_ninetySevenCQ_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_ninetySevenCQ_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_ninetySevenCQ_3347 : Nat.Prime 3347 := by norm_num

private theorem prime_ninetySevenCQ_3391 : Nat.Prime 3391 := by norm_num

private theorem prime_ninetySevenCQ_3407 : Nat.Prime 3407 := by norm_num

private theorem prime_ninetySevenCQ_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_ninetySevenCQ_3463 : Nat.Prime 3463 := by norm_num

private theorem prime_ninetySevenCQ_3499 : Nat.Prime 3499 := by norm_num

private theorem prime_ninetySevenCQ_3533 : Nat.Prime 3533 := by norm_num

private theorem prime_ninetySevenCQ_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_ninetySevenCQ_3637 : Nat.Prime 3637 := by norm_num

private theorem prime_ninetySevenCQ_3797 : Nat.Prime 3797 := by norm_num

private theorem prime_ninetySevenCQ_3919 : Nat.Prime 3919 := by norm_num

private theorem prime_ninetySevenCQ_4099 : Nat.Prime 4099 := by norm_num

private theorem prime_ninetySevenCQ_4133 : Nat.Prime 4133 := by norm_num

private theorem prime_ninetySevenCQ_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_ninetySevenCQ_4271 : Nat.Prime 4271 := by norm_num

private theorem prime_ninetySevenCQ_4483 : Nat.Prime 4483 := by norm_num

private theorem prime_ninetySevenCQ_4513 : Nat.Prime 4513 := by norm_num

private theorem prime_ninetySevenCQ_4519 : Nat.Prime 4519 := by norm_num

private theorem prime_ninetySevenCQ_4679 : Nat.Prime 4679 := by norm_num

private theorem prime_ninetySevenCQ_4721 : Nat.Prime 4721 := by norm_num

private theorem prime_ninetySevenCQ_4733 : Nat.Prime 4733 := by norm_num

private theorem prime_ninetySevenCQ_5011 : Nat.Prime 5011 := by norm_num

private theorem prime_ninetySevenCQ_5039 : Nat.Prime 5039 := by norm_num

private theorem prime_ninetySevenCQ_5077 : Nat.Prime 5077 := by norm_num

private theorem prime_ninetySevenCQ_5197 : Nat.Prime 5197 := by norm_num

private theorem prime_ninetySevenCQ_5693 : Nat.Prime 5693 := by norm_num

private theorem prime_ninetySevenCQ_5711 : Nat.Prime 5711 := by norm_num

private theorem prime_ninetySevenCQ_5939 : Nat.Prime 5939 := by norm_num

private theorem prime_ninetySevenCQ_6073 : Nat.Prime 6073 := by norm_num

private theorem prime_ninetySevenCQ_6079 : Nat.Prime 6079 := by norm_num

private theorem prime_ninetySevenCQ_6563 : Nat.Prime 6563 := by norm_num

private theorem prime_ninetySevenCQ_6659 : Nat.Prime 6659 := by norm_num

private theorem prime_ninetySevenCQ_6823 : Nat.Prime 6823 := by norm_num

private theorem prime_ninetySevenCQ_6899 : Nat.Prime 6899 := by norm_num

private theorem prime_ninetySevenCQ_7151 : Nat.Prime 7151 := by norm_num

private theorem prime_ninetySevenCQ_7573 : Nat.Prime 7573 := by norm_num

private theorem prime_ninetySevenCQ_7589 : Nat.Prime 7589 := by norm_num

private theorem prime_ninetySevenCQ_8101 : Nat.Prime 8101 := by norm_num

private theorem prime_ninetySevenCQ_8311 : Nat.Prime 8311 := by norm_num

private theorem prime_ninetySevenCQ_8623 : Nat.Prime 8623 := by norm_num

private theorem prime_ninetySevenCQ_8699 : Nat.Prime 8699 := by norm_num

private theorem prime_ninetySevenCQ_8971 : Nat.Prime 8971 := by norm_num

private theorem prime_ninetySevenCQ_9007 : Nat.Prime 9007 := by norm_num

private theorem prime_ninetySevenCQ_9337 : Nat.Prime 9337 := by norm_num

private theorem prime_ninetySevenCQ_9371 : Nat.Prime 9371 := by norm_num

private theorem prime_ninetySevenCQ_9421 : Nat.Prime 9421 := by norm_num

private theorem prime_ninetySevenCQ_9479 : Nat.Prime 9479 := by norm_num

private theorem prime_ninetySevenCQ_9551 : Nat.Prime 9551 := by norm_num

private theorem prime_ninetySevenCQ_9677 : Nat.Prime 9677 := by norm_num

private theorem prime_ninetySevenCQ_10181 : Nat.Prime 10181 := by norm_num

private theorem prime_ninetySevenCQ_10289 : Nat.Prime 10289 := by norm_num

private theorem prime_ninetySevenCQ_10429 : Nat.Prime 10429 := by norm_num

private theorem prime_ninetySevenCQ_10607 : Nat.Prime 10607 := by norm_num

private theorem prime_ninetySevenCQ_10631 : Nat.Prime 10631 := by norm_num

private theorem prime_ninetySevenCQ_12107 : Nat.Prime 12107 := by norm_num

private theorem prime_ninetySevenCQ_12451 : Nat.Prime 12451 := by norm_num

private theorem prime_ninetySevenCQ_12917 : Nat.Prime 12917 := by norm_num

private theorem prime_ninetySevenCQ_12953 : Nat.Prime 12953 := by norm_num

private theorem prime_ninetySevenCQ_13597 : Nat.Prime 13597 := by norm_num

private theorem prime_ninetySevenCQ_14389 : Nat.Prime 14389 := by norm_num

private theorem prime_ninetySevenCQ_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_ninetySevenCQ_15313 : Nat.Prime 15313 := by norm_num

private theorem prime_ninetySevenCQ_15901 : Nat.Prime 15901 := by norm_num

private theorem prime_ninetySevenCQ_16183 : Nat.Prime 16183 := by norm_num

private theorem prime_ninetySevenCQ_16267 : Nat.Prime 16267 := by norm_num

private theorem prime_ninetySevenCQ_16301 : Nat.Prime 16301 := by norm_num

private theorem prime_ninetySevenCQ_16831 : Nat.Prime 16831 := by norm_num

private theorem prime_ninetySevenCQ_17401 : Nat.Prime 17401 := by norm_num

private theorem prime_ninetySevenCQ_17483 : Nat.Prime 17483 := by norm_num

private theorem prime_ninetySevenCQ_18199 : Nat.Prime 18199 := by norm_num

private theorem prime_ninetySevenCQ_18287 : Nat.Prime 18287 := by norm_num

private theorem prime_ninetySevenCQ_18517 : Nat.Prime 18517 := by norm_num

private theorem prime_ninetySevenCQ_18617 : Nat.Prime 18617 := by norm_num

private theorem prime_ninetySevenCQ_18773 : Nat.Prime 18773 := by norm_num

private theorem prime_ninetySevenCQ_18803 : Nat.Prime 18803 := by norm_num

private theorem prime_ninetySevenCQ_19031 : Nat.Prime 19031 := by norm_num

private theorem prime_ninetySevenCQ_19037 : Nat.Prime 19037 := by norm_num

private theorem prime_ninetySevenCQ_20543 : Nat.Prime 20543 := by norm_num

private theorem prime_ninetySevenCQ_21499 : Nat.Prime 21499 := by norm_num

private theorem prime_ninetySevenCQ_21803 : Nat.Prime 21803 := by norm_num

private theorem prime_ninetySevenCQ_23143 : Nat.Prime 23143 := by norm_num

private theorem prime_ninetySevenCQ_23609 : Nat.Prime 23609 := by norm_num

private theorem prime_ninetySevenCQ_23671 : Nat.Prime 23671 := by norm_num

private theorem prime_ninetySevenCQ_23993 : Nat.Prime 23993 := by norm_num

private theorem prime_ninetySevenCQ_24007 : Nat.Prime 24007 := by norm_num

private theorem prime_ninetySevenCQ_24691 : Nat.Prime 24691 := by norm_num

private theorem prime_ninetySevenCQ_24749 : Nat.Prime 24749 := by norm_num

private theorem prime_ninetySevenCQ_25357 : Nat.Prime 25357 := by norm_num

private theorem prime_ninetySevenCQ_25841 : Nat.Prime 25841 := by norm_num

private theorem prime_ninetySevenCQ_26267 : Nat.Prime 26267 := by norm_num

private theorem prime_ninetySevenCQ_26921 : Nat.Prime 26921 := by norm_num

private theorem prime_ninetySevenCQ_27017 : Nat.Prime 27017 := by norm_num

private theorem prime_ninetySevenCQ_28631 : Nat.Prime 28631 := by norm_num

private theorem prime_ninetySevenCQ_29023 : Nat.Prime 29023 := by norm_num

private theorem prime_ninetySevenCQ_29221 : Nat.Prime 29221 := by norm_num

private theorem prime_ninetySevenCQ_30631 : Nat.Prime 30631 := by norm_num

private theorem prime_ninetySevenCQ_33457 : Nat.Prime 33457 := by norm_num

private theorem prime_ninetySevenCQ_34213 : Nat.Prime 34213 := by norm_num

private theorem prime_ninetySevenCQ_34421 : Nat.Prime 34421 := by norm_num

private theorem prime_ninetySevenCQ_34631 : Nat.Prime 34631 := by norm_num

private theorem prime_ninetySevenCQ_36671 : Nat.Prime 36671 := by norm_num

private theorem prime_ninetySevenCQ_37573 : Nat.Prime 37573 := by norm_num

private theorem prime_ninetySevenCQ_41443 : Nat.Prime 41443 := by norm_num

private theorem prime_ninetySevenCQ_42221 : Nat.Prime 42221 := by norm_num

private theorem prime_ninetySevenCQ_42727 : Nat.Prime 42727 := by norm_num

private theorem prime_ninetySevenCQ_46279 : Nat.Prime 46279 := by norm_num

private theorem prime_ninetySevenCQ_47977 : Nat.Prime 47977 := by norm_num

private theorem prime_ninetySevenCQ_48809 : Nat.Prime 48809 := by norm_num

private theorem prime_ninetySevenCQ_49789 : Nat.Prime 49789 := by norm_num

private theorem prime_ninetySevenCQ_50893 : Nat.Prime 50893 := by norm_num

private theorem prime_ninetySevenCQ_52837 : Nat.Prime 52837 := by norm_num

private theorem prime_ninetySevenCQ_53233 : Nat.Prime 53233 := by norm_num

private theorem prime_ninetySevenCQ_55117 : Nat.Prime 55117 := by norm_num

private theorem prime_ninetySevenCQ_55351 : Nat.Prime 55351 := by norm_num

private theorem prime_ninetySevenCQ_56929 : Nat.Prime 56929 := by norm_num

private theorem prime_ninetySevenCQ_59621 : Nat.Prime 59621 := by norm_num

private theorem prime_ninetySevenCQ_59707 : Nat.Prime 59707 := by norm_num

private theorem prime_ninetySevenCQ_62171 : Nat.Prime 62171 := by norm_num

private theorem prime_ninetySevenCQ_63629 : Nat.Prime 63629 := by norm_num

private theorem prime_ninetySevenCQ_64499 : Nat.Prime 64499 := by norm_num

private theorem prime_ninetySevenCQ_64919 : Nat.Prime 64919 := by norm_num

private theorem prime_ninetySevenCQ_65609 : Nat.Prime 65609 := by norm_num

private theorem prime_ninetySevenCQ_67699 : Nat.Prime 67699 := by norm_num

private theorem prime_ninetySevenCQ_67961 : Nat.Prime 67961 := by norm_num

private theorem prime_ninetySevenCQ_69317 : Nat.Prime 69317 := by norm_num

private theorem prime_ninetySevenCQ_70621 : Nat.Prime 70621 := by norm_num

private theorem prime_ninetySevenCQ_74551 : Nat.Prime 74551 := by norm_num

private theorem prime_ninetySevenCQ_76781 : Nat.Prime 76781 := by norm_num

private theorem prime_ninetySevenCQ_79111 : Nat.Prime 79111 := by norm_num

private theorem prime_ninetySevenCQ_81883 : Nat.Prime 81883 := by norm_num

private theorem prime_ninetySevenCQ_82549 : Nat.Prime 82549 := by norm_num

private theorem prime_ninetySevenCQ_84143 : Nat.Prime 84143 := by norm_num

private theorem prime_ninetySevenCQ_86929 : Nat.Prime 86929 := by norm_num

private theorem prime_ninetySevenCQ_90901 : Nat.Prime 90901 := by norm_num

private theorem prime_ninetySevenCQ_91183 : Nat.Prime 91183 := by norm_num

private theorem prime_ninetySevenCQ_94441 : Nat.Prime 94441 := by norm_num

private theorem prime_ninetySevenCQ_98981 : Nat.Prime 98981 := by norm_num

private theorem prime_ninetySevenCQ_101939 : Nat.Prime 101939 := by norm_num

private theorem prime_ninetySevenCQ_107101 : Nat.Prime 107101 := by norm_num

private theorem prime_ninetySevenCQ_122579 : Nat.Prime 122579 := by norm_num

private theorem prime_ninetySevenCQ_124721 : Nat.Prime 124721 := by norm_num

private theorem prime_ninetySevenCQ_125651 : Nat.Prime 125651 := by norm_num

private theorem prime_ninetySevenCQ_133669 : Nat.Prime 133669 := by norm_num

private theorem prime_ninetySevenCQ_134591 : Nat.Prime 134591 := by norm_num

private theorem prime_ninetySevenCQ_135649 : Nat.Prime 135649 := by norm_num

private theorem prime_ninetySevenCQ_137573 : Nat.Prime 137573 := by norm_num

private theorem prime_ninetySevenCQ_138461 : Nat.Prime 138461 := by norm_num

private theorem prime_ninetySevenCQ_141853 : Nat.Prime 141853 := by norm_num

private theorem prime_ninetySevenCQ_145949 : Nat.Prime 145949 := by norm_num

private theorem prime_ninetySevenCQ_147341 : Nat.Prime 147341 := by norm_num

private theorem prime_ninetySevenCQ_148711 : Nat.Prime 148711 := by norm_num

private theorem prime_ninetySevenCQ_149183 : Nat.Prime 149183 := by norm_num

private theorem prime_ninetySevenCQ_149873 : Nat.Prime 149873 := by norm_num

private theorem prime_ninetySevenCQ_155599 : Nat.Prime 155599 := by norm_num

private theorem prime_ninetySevenCQ_159167 : Nat.Prime 159167 := by norm_num

private theorem prime_ninetySevenCQ_159977 : Nat.Prime 159977 := by norm_num

private theorem prime_ninetySevenCQ_164249 : Nat.Prime 164249 := by norm_num

private theorem prime_ninetySevenCQ_164363 : Nat.Prime 164363 := by norm_num

private theorem prime_ninetySevenCQ_165569 : Nat.Prime 165569 := by norm_num

private theorem prime_ninetySevenCQ_168769 : Nat.Prime 168769 := by norm_num

private theorem prime_ninetySevenCQ_169063 : Nat.Prime 169063 := by norm_num

private theorem prime_ninetySevenCQ_172027 : Nat.Prime 172027 := by norm_num

private theorem prime_ninetySevenCQ_185749 : Nat.Prime 185749 := by norm_num

private theorem prime_ninetySevenCQ_190529 : Nat.Prime 190529 := by norm_num

private theorem prime_ninetySevenCQ_193939 : Nat.Prime 193939 := by norm_num

private theorem prime_ninetySevenCQ_212437 : Nat.Prime 212437 := by norm_num

private theorem prime_ninetySevenCQ_223441 : Nat.Prime 223441 := by norm_num

private theorem prime_ninetySevenCQ_235811 : Nat.Prime 235811 := by norm_num

private theorem prime_ninetySevenCQ_247609 : Nat.Prime 247609 := by norm_num

private theorem prime_ninetySevenCQ_269419 : Nat.Prime 269419 := by norm_num

private theorem prime_ninetySevenCQ_270667 : Nat.Prime 270667 := by norm_num

private theorem prime_ninetySevenCQ_280843 : Nat.Prime 280843 := by norm_num

private theorem prime_ninetySevenCQ_282563 : Nat.Prime 282563 := by norm_num

private theorem prime_ninetySevenCQ_285569 : Nat.Prime 285569 := by norm_num

private theorem prime_ninetySevenCQ_318103 : Nat.Prime 318103 := by norm_num

private theorem prime_ninetySevenCQ_335557 : Nat.Prime 335557 := by norm_num

private theorem prime_ninetySevenCQ_406579 : Nat.Prime 406579 := by norm_num

private theorem prime_ninetySevenCQ_423461 : Nat.Prime 423461 := by norm_num

private theorem prime_ninetySevenCQ_471091 : Nat.Prime 471091 := by norm_num

private theorem prime_ninetySevenCQ_488981 : Nat.Prime 488981 := by norm_num

private theorem prime_ninetySevenCQ_554633 : Nat.Prime 554633 := by norm_num

private theorem prime_ninetySevenCQ_567257 : Nat.Prime 567257 := by norm_num

private theorem prime_ninetySevenCQ_575593 : Nat.Prime 575593 := by norm_num

private theorem prime_ninetySevenCQ_581311 : Nat.Prime 581311 := by norm_num

private theorem prime_ninetySevenCQ_593429 : Nat.Prime 593429 := by norm_num

private theorem prime_ninetySevenCQ_661883 : Nat.Prime 661883 := by norm_num

private theorem prime_ninetySevenCQ_741053 : Nat.Prime 741053 := by norm_num

private theorem prime_ninetySevenCQ_793487 : Nat.Prime 793487 := by norm_num

private theorem prime_ninetySevenCQ_797747 : Nat.Prime 797747 := by norm_num

private theorem prime_ninetySevenCQ_806503 : Nat.Prime 806503 := by norm_num

private theorem prime_ninetySevenCQ_827147 : Nat.Prime 827147 := by norm_num

private theorem prime_ninetySevenCQ_840457 : Nat.Prime 840457 := by norm_num

private theorem prime_ninetySevenCQ_881681 : Nat.Prime 881681 := by norm_num

private theorem prime_ninetySevenCQ_978473 : Nat.Prime 978473 := by norm_num

private theorem prime_ninetySevenCQ_1005553 : Nat.Prime 1005553 := by norm_num

private theorem prime_ninetySevenCQ_1011221 : Nat.Prime 1011221 := by norm_num

private theorem prime_ninetySevenCQ_1045151 : Nat.Prime 1045151 := by norm_num

private theorem prime_ninetySevenCQ_1147231 : Nat.Prime 1147231 := by norm_num

private theorem prime_ninetySevenCQ_1211563 : Nat.Prime 1211563 := by norm_num

private theorem prime_ninetySevenCQ_1226387 : Nat.Prime 1226387 := by norm_num

private theorem prime_ninetySevenCQ_1266487 : Nat.Prime 1266487 := by norm_num

private theorem prime_ninetySevenCQ_1281433 : Nat.Prime 1281433 := by norm_num

private theorem prime_ninetySevenCQ_1304539 : Nat.Prime 1304539 := by norm_num

private theorem prime_ninetySevenCQ_1499287 : Nat.Prime 1499287 := by norm_num

private theorem prime_ninetySevenCQ_1506551 : Nat.Prime 1506551 := by norm_num

private theorem prime_ninetySevenCQ_1901117 : Nat.Prime 1901117 := by norm_num

private theorem prime_ninetySevenCQ_1906613 : Nat.Prime 1906613 := by norm_num

private theorem prime_ninetySevenCQ_1945057 : Nat.Prime 1945057 := by norm_num

private theorem prime_ninetySevenCQ_1968257 : Nat.Prime 1968257 := by norm_num

private theorem prime_ninetySevenCQ_1990607 : Nat.Prime 1990607 := by norm_num

private theorem prime_ninetySevenCQ_2135831 : Nat.Prime 2135831 := by norm_num

private theorem prime_ninetySevenCQ_2140169 : Nat.Prime 2140169 := by norm_num

private theorem prime_ninetySevenCQ_2253683 : Nat.Prime 2253683 := by norm_num

private theorem prime_ninetySevenCQ_2304527 : Nat.Prime 2304527 := by norm_num

private theorem prime_ninetySevenCQ_2339089 : Nat.Prime 2339089 := by norm_num

private theorem prime_ninetySevenCQ_2365093 : Nat.Prime 2365093 := by norm_num

private theorem prime_ninetySevenCQ_2415871 : Nat.Prime 2415871 := by norm_num

private theorem prime_ninetySevenCQ_2594971 : Nat.Prime 2594971 := by norm_num

private theorem prime_ninetySevenCQ_2817169 : Nat.Prime 2817169 := by norm_num

private theorem prime_ninetySevenCQ_3032417 : Nat.Prime 3032417 := by norm_num

private theorem prime_ninetySevenCQ_3312107 : Nat.Prime 3312107 := by norm_num

private theorem prime_ninetySevenCQ_3868219 : Nat.Prime 3868219 := by norm_num

private theorem prime_ninetySevenCQ_3883073 : Nat.Prime 3883073 := by norm_num

private theorem prime_ninetySevenCQ_3941887 : Nat.Prime 3941887 := by norm_num

private theorem prime_ninetySevenCQ_4154077 : Nat.Prime 4154077 := by norm_num

private theorem prime_ninetySevenCQ_4344517 : Nat.Prime 4344517 := by norm_num

private theorem prime_ninetySevenCQ_4484743 : Nat.Prime 4484743 := by norm_num

private theorem prime_ninetySevenCQ_4523791 : Nat.Prime 4523791 := by norm_num

private theorem prime_ninetySevenCQ_4528093 : Nat.Prime 4528093 := by norm_num

private theorem prime_ninetySevenCQ_4555997 : Nat.Prime 4555997 := by norm_num

private theorem prime_ninetySevenCQ_4642081 : Nat.Prime 4642081 := by norm_num

private theorem prime_ninetySevenCQ_4683499 : Nat.Prime 4683499 := by norm_num

private theorem prime_ninetySevenCQ_4889933 : Nat.Prime 4889933 := by norm_num

private theorem prime_ninetySevenCQ_5136011 : Nat.Prime 5136011 := by norm_num

private theorem prime_ninetySevenCQ_5156839 : Nat.Prime 5156839 := by norm_num

private theorem prime_ninetySevenCQ_5181101 : Nat.Prime 5181101 := by norm_num

private theorem prime_ninetySevenCQ_5361827 : Nat.Prime 5361827 := by norm_num

private theorem prime_ninetySevenCQ_5387059 : Nat.Prime 5387059 := by norm_num

private theorem prime_ninetySevenCQ_5462647 : Nat.Prime 5462647 := by norm_num

private theorem prime_ninetySevenCQ_5718899 : Nat.Prime 5718899 := by norm_num

private theorem prime_ninetySevenCQ_6465653 : Nat.Prime 6465653 := by norm_num

private theorem prime_ninetySevenCQ_6523757 : Nat.Prime 6523757 := by norm_num

private theorem prime_ninetySevenCQ_6546767 : Nat.Prime 6546767 := by norm_num

private theorem prime_ninetySevenCQ_6559337 : Nat.Prime 6559337 := by norm_num

private theorem prime_ninetySevenCQ_6683519 : Nat.Prime 6683519 := by norm_num

private theorem prime_ninetySevenCQ_6691403 : Nat.Prime 6691403 := by norm_num

private theorem prime_ninetySevenCQ_6698291 : Nat.Prime 6698291 := by norm_num

private theorem prime_ninetySevenCQ_6807901 : Nat.Prime 6807901 := by norm_num

private theorem prime_ninetySevenCQ_6961151 : Nat.Prime 6961151 := by norm_num

private theorem prime_ninetySevenCQ_7387643 : Nat.Prime 7387643 := by norm_num

private theorem prime_ninetySevenCQ_8611903 : Nat.Prime 8611903 := by norm_num

private theorem prime_ninetySevenCQ_8806073 : Nat.Prime 8806073 := by norm_num

private theorem prime_ninetySevenCQ_8975503 : Nat.Prime 8975503 := by norm_num

private theorem prime_ninetySevenCQ_9168721 : Nat.Prime 9168721 := by norm_num

private theorem prime_ninetySevenCQ_9242983 : Nat.Prime 9242983 := by norm_num

private theorem prime_ninetySevenCQ_9361613 : Nat.Prime 9361613 := by norm_num

private theorem prime_ninetySevenCQ_10079647 : Nat.Prime 10079647 := by norm_num

private theorem prime_ninetySevenCQ_10864627 : Nat.Prime 10864627 := by norm_num

private theorem prime_ninetySevenCQ_10896461 : Nat.Prime 10896461 := by norm_num

private theorem prime_ninetySevenCQ_11741759 : Nat.Prime 11741759 := by norm_num

private theorem prime_ninetySevenCQ_12366023 : Nat.Prime 12366023 := by norm_num

private theorem prime_ninetySevenCQ_12575711 : Nat.Prime 12575711 := by norm_num

private theorem prime_ninetySevenCQ_12721663 : Nat.Prime 12721663 := by norm_num

private theorem prime_ninetySevenCQ_13317709 : Nat.Prime 13317709 := by norm_num

private theorem prime_ninetySevenCQ_13619087 : Nat.Prime 13619087 := by norm_num

private theorem prime_ninetySevenCQ_15118673 : Nat.Prime 15118673 := by norm_num

private theorem prime_ninetySevenCQ_16541093 : Nat.Prime 16541093 := by norm_num

private theorem prime_ninetySevenCQ_18403327 : Nat.Prime 18403327 := by norm_num

private theorem prime_ninetySevenCQ_20825647 : Nat.Prime 20825647 := by norm_num

private theorem prime_ninetySevenCQ_22673663 : Nat.Prime 22673663 := by norm_num

private theorem prime_ninetySevenCQ_24738797 : Nat.Prime 24738797 := by norm_num

private theorem prime_ninetySevenCQ_25683653 : Nat.Prime 25683653 := by norm_num

private theorem prime_ninetySevenCQ_25723679 : Nat.Prime 25723679 := by norm_num

private theorem prime_ninetySevenCQ_26138867 : Nat.Prime 26138867 := by norm_num

private theorem prime_ninetySevenCQ_26188867 : Nat.Prime 26188867 := by norm_num

private theorem prime_ninetySevenCQ_26706671 : Nat.Prime 26706671 := by norm_num

private theorem prime_ninetySevenCQ_27457501 : Nat.Prime 27457501 := by norm_num

private theorem prime_ninetySevenCQ_29825651 : Nat.Prime 29825651 := by norm_num

private theorem prime_ninetySevenCQ_32989477 : Nat.Prime 32989477 := by
  apply lucas_primality 32989477 (2 : ZMod 32989477)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (16267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (16267, 1)] : List FactorBlock).map factorBlockValue).prod) = 32989477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_16267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32989477) ^ 16494738 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32989477) ^ 10996492 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32989477) ^ 2537652 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32989477) ^ 2028 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_35791559 : Nat.Prime 35791559 := by
  apply lucas_primality 35791559 (11 : ZMod 35791559)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (131, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (131, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) = 35791559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_131
      · exact prime_ninetySevenCQ_1129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 35791559) ^ 17895779 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 35791559) ^ 3253778 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 35791559) ^ 273218 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 35791559) ^ 31702 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_41300317 : Nat.Prime 41300317 := by
  apply lucas_primality 41300317 (5 : ZMod 41300317)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1147231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1147231, 1)] : List FactorBlock).map factorBlockValue).prod) = 41300317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_1147231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 41300317) ^ 20650158 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 41300317) ^ 13766772 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 41300317) ^ 36 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_46205461 : Nat.Prime 46205461 := by
  apply lucas_primality 46205461 (2 : ZMod 46205461)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (36671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (36671, 1)] : List FactorBlock).map factorBlockValue).prod) = 46205461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_36671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46205461) ^ 23102730 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 46205461) ^ 15401820 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 46205461) ^ 9241092 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 46205461) ^ 6600780 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 46205461) ^ 1260 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_46886269 : Nat.Prime 46886269 := by
  apply lucas_primality 46886269 (6 : ZMod 46886269)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (89, 1), (307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (89, 1), (307, 1)] : List FactorBlock).map factorBlockValue).prod) = 46886269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_89
      · exact prime_ninetySevenCQ_307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 46886269) ^ 23443134 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 46886269) ^ 15628756 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 46886269) ^ 4262388 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 46886269) ^ 3606636 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 46886269) ^ 526812 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 46886269) ^ 152724 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_53834497 : Nat.Prime 53834497 := by
  apply lucas_primality 53834497 (5 : ZMod 53834497)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (191, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (191, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod) = 53834497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_191
      · exact prime_ninetySevenCQ_367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 53834497) ^ 26917248 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 53834497) ^ 17944832 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 53834497) ^ 281856 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 53834497) ^ 146688 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_59338231 : Nat.Prime 59338231 := by
  apply lucas_primality 59338231 (3 : ZMod 59338231)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (282563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (282563, 1)] : List FactorBlock).map factorBlockValue).prod) = 59338231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_282563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 59338231) ^ 29669115 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 59338231) ^ 19779410 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 59338231) ^ 11867646 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 59338231) ^ 8476890 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 59338231) ^ 210 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_60839239 : Nat.Prime 60839239 := by
  apply lucas_primality 60839239 (3 : ZMod 60839239)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (235811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (235811, 1)] : List FactorBlock).map factorBlockValue).prod) = 60839239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_43
      · exact prime_ninetySevenCQ_235811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 60839239) ^ 30419619 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 60839239) ^ 20279746 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 60839239) ^ 1414866 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 60839239) ^ 258 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_68705867 : Nat.Prime 68705867 := by
  apply lucas_primality 68705867 (2 : ZMod 68705867)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (257, 1), (133669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (257, 1), (133669, 1)] : List FactorBlock).map factorBlockValue).prod) = 68705867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_257
      · exact prime_ninetySevenCQ_133669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68705867) ^ 34352933 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68705867) ^ 267338 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68705867) ^ 514 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_70906357 : Nat.Prime 70906357 := by
  apply lucas_primality 70906357 (2 : ZMod 70906357)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (37, 1), (53233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (37, 1), (53233, 1)] : List FactorBlock).map factorBlockValue).prod) = 70906357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_37
      · exact prime_ninetySevenCQ_53233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70906357) ^ 35453178 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 70906357) ^ 23635452 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 70906357) ^ 1916388 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 70906357) ^ 1332 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_73053691 : Nat.Prime 73053691 := by
  apply lucas_primality 73053691 (7 : ZMod 73053691)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (293, 1), (8311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (293, 1), (8311, 1)] : List FactorBlock).map factorBlockValue).prod) = 73053691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_293
      · exact prime_ninetySevenCQ_8311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 73053691) ^ 36526845 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73053691) ^ 24351230 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73053691) ^ 14610738 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73053691) ^ 249330 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73053691) ^ 8790 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_73256489 : Nat.Prime 73256489 := by
  apply lucas_primality 73256489 (3 : ZMod 73256489)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (487, 1), (18803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (487, 1), (18803, 1)] : List FactorBlock).map factorBlockValue).prod) = 73256489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_487
      · exact prime_ninetySevenCQ_18803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 73256489) ^ 36628244 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73256489) ^ 150424 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73256489) ^ 3896 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_77661461 : Nat.Prime 77661461 := by
  apply lucas_primality 77661461 (2 : ZMod 77661461)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3883073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3883073, 1)] : List FactorBlock).map factorBlockValue).prod) = 77661461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_3883073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 77661461) ^ 38830730 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 77661461) ^ 15532292 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 77661461) ^ 20 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_79529027 : Nat.Prime 79529027 := by
  apply lucas_primality 79529027 (2 : ZMod 79529027)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2339089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2339089, 1)] : List FactorBlock).map factorBlockValue).prod) = 79529027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_2339089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 79529027) ^ 39764513 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 79529027) ^ 4678178 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 79529027) ^ 34 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_99304649 : Nat.Prime 99304649 := by
  apply lucas_primality 99304649 (3 : ZMod 99304649)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3413, 1), (3637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3413, 1), (3637, 1)] : List FactorBlock).map factorBlockValue).prod) = 99304649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3413
      · exact prime_ninetySevenCQ_3637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 99304649) ^ 49652324 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 99304649) ^ 29096 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 99304649) ^ 27304 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_101666563 : Nat.Prime 101666563 := by
  apply lucas_primality 101666563 (3 : ZMod 101666563)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (103, 1), (9677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (103, 1), (9677, 1)] : List FactorBlock).map factorBlockValue).prod) = 101666563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_103
      · exact prime_ninetySevenCQ_9677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 101666563) ^ 50833281 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 101666563) ^ 33888854 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 101666563) ^ 5980386 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 101666563) ^ 987054 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 101666563) ^ 10506 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_107260333 : Nat.Prime 107260333 := by
  apply lucas_primality 107260333 (2 : ZMod 107260333)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (149, 1), (239, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (149, 1), (239, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) = 107260333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_149
      · exact prime_ninetySevenCQ_239
      · exact prime_ninetySevenCQ_251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 107260333) ^ 53630166 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 107260333) ^ 35753444 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 107260333) ^ 719868 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 107260333) ^ 448788 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 107260333) ^ 427332 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_109037911 : Nat.Prime 109037911 := by
  apply lucas_primality 109037911 (3 : ZMod 109037911)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (73, 1), (49789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (73, 1), (49789, 1)] : List FactorBlock).map factorBlockValue).prod) = 109037911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_73
      · exact prime_ninetySevenCQ_49789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 109037911) ^ 54518955 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 109037911) ^ 36345970 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 109037911) ^ 21807582 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 109037911) ^ 1493670 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 109037911) ^ 2190 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_115841633 : Nat.Prime 115841633 := by
  apply lucas_primality 115841633 (3 : ZMod 115841633)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (190529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (190529, 1)] : List FactorBlock).map factorBlockValue).prod) = 115841633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_190529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 115841633) ^ 57920816 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 115841633) ^ 6096928 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 115841633) ^ 608 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_124882273 : Nat.Prime 124882273 := by
  apply lucas_primality 124882273 (7 : ZMod 124882273)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (17, 1), (23, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (17, 1), (23, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 124882273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 124882273) ^ 62441136 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 124882273) ^ 41627424 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 124882273) ^ 7346016 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 124882273) ^ 5429664 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 124882273) ^ 112608 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_130252379 : Nat.Prime 130252379 := by
  apply lucas_primality 130252379 (2 : ZMod 130252379)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4253, 1), (15313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4253, 1), (15313, 1)] : List FactorBlock).map factorBlockValue).prod) = 130252379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_4253
      · exact prime_ninetySevenCQ_15313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 130252379) ^ 65126189 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 130252379) ^ 30626 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 130252379) ^ 8506 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_136041979 : Nat.Prime 136041979 := by
  apply lucas_primality 136041979 (10 : ZMod 136041979)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22673663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22673663, 1)] : List FactorBlock).map factorBlockValue).prod) = 136041979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_22673663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 136041979) ^ 68020989 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 136041979) ^ 45347326 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 136041979) ^ 6 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_146219443 : Nat.Prime 146219443 := by
  apply lucas_primality 146219443 (2 : ZMod 146219443)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (383, 1), (63629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (383, 1), (63629, 1)] : List FactorBlock).map factorBlockValue).prod) = 146219443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_383
      · exact prime_ninetySevenCQ_63629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 146219443) ^ 73109721 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 146219443) ^ 48739814 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 146219443) ^ 381774 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 146219443) ^ 2298 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_146512979 : Nat.Prime 146512979 := by
  apply lucas_primality 146512979 (2 : ZMod 146512979)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73256489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73256489, 1)] : List FactorBlock).map factorBlockValue).prod) = 146512979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_73256489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 146512979) ^ 73256489 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 146512979) ^ 2 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_159260771 : Nat.Prime 159260771 := by
  apply lucas_primality 159260771 (6 : ZMod 159260771)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (977, 1), (16301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (977, 1), (16301, 1)] : List FactorBlock).map factorBlockValue).prod) = 159260771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_977
      · exact prime_ninetySevenCQ_16301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 159260771) ^ 79630385 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 159260771) ^ 31852154 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 159260771) ^ 163010 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 159260771) ^ 9770 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_160240027 : Nat.Prime 160240027 := by
  apply lucas_primality 160240027 (2 : ZMod 160240027)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (26706671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (26706671, 1)] : List FactorBlock).map factorBlockValue).prod) = 160240027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_26706671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 160240027) ^ 80120013 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 160240027) ^ 53413342 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 160240027) ^ 6 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_171566971 : Nat.Prime 171566971 := by
  apply lucas_primality 171566971 (3 : ZMod 171566971)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5718899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5718899, 1)] : List FactorBlock).map factorBlockValue).prod) = 171566971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_5718899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 171566971) ^ 85783485 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 171566971) ^ 57188990 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 171566971) ^ 34313394 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 171566971) ^ 30 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_173124323 : Nat.Prime 173124323 := by
  apply lucas_primality 173124323 (2 : ZMod 173124323)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (12366023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (12366023, 1)] : List FactorBlock).map factorBlockValue).prod) = 173124323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_12366023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 173124323) ^ 86562161 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173124323) ^ 24732046 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173124323) ^ 14 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_173489567 : Nat.Prime 173489567 := by
  apply lucas_primality 173489567 (5 : ZMod 173489567)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (467, 1), (185749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (467, 1), (185749, 1)] : List FactorBlock).map factorBlockValue).prod) = 173489567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_467
      · exact prime_ninetySevenCQ_185749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 173489567) ^ 86744783 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 173489567) ^ 371498 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 173489567) ^ 934 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_173833181 : Nat.Prime 173833181 := by
  apply lucas_primality 173833181 (2 : ZMod 173833181)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (79, 1), (269, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (79, 1), (269, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) = 173833181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_79
      · exact prime_ninetySevenCQ_269
      · exact prime_ninetySevenCQ_409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 173833181) ^ 86916590 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173833181) ^ 34766636 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173833181) ^ 2200420 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173833181) ^ 646220 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173833181) ^ 425020 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_183160007 : Nat.Prime 183160007 := by
  apply lucas_primality 183160007 (5 : ZMod 183160007)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (5387059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (5387059, 1)] : List FactorBlock).map factorBlockValue).prod) = 183160007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_5387059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 183160007) ^ 91580003 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 183160007) ^ 10774118 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 183160007) ^ 34 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_189757027 : Nat.Prime 189757027 := by
  apply lucas_primality 189757027 (3 : ZMod 189757027)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (97, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (97, 1), (2131, 1)] : List FactorBlock).map factorBlockValue).prod) = 189757027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_97
      · exact prime_ninetySevenCQ_2131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 189757027) ^ 94878513 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 189757027) ^ 63252342 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 189757027) ^ 11162178 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 189757027) ^ 1956258 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 189757027) ^ 89046 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_190667219 : Nat.Prime 190667219 := by
  apply lucas_primality 190667219 (2 : ZMod 190667219)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13619087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13619087, 1)] : List FactorBlock).map factorBlockValue).prod) = 190667219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_13619087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 190667219) ^ 95333609 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 190667219) ^ 27238174 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 190667219) ^ 14 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_206703113 : Nat.Prime 206703113 := by
  apply lucas_primality 206703113 (3 : ZMod 206703113)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (335557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (335557, 1)] : List FactorBlock).map factorBlockValue).prod) = 206703113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_335557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 206703113) ^ 103351556 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 206703113) ^ 29529016 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 206703113) ^ 18791192 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 206703113) ^ 616 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_231575303 : Nat.Prime 231575303 := by
  apply lucas_primality 231575303 (5 : ZMod 231575303)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (16541093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (16541093, 1)] : List FactorBlock).map factorBlockValue).prod) = 231575303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_16541093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 231575303) ^ 115787651 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 231575303) ^ 33082186 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 231575303) ^ 14 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_231683267 : Nat.Prime 231683267 := by
  apply lucas_primality 231683267 (2 : ZMod 231683267)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (115841633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (115841633, 1)] : List FactorBlock).map factorBlockValue).prod) = 231683267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_115841633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 231683267) ^ 115841633 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 231683267) ^ 2 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_239890093 : Nat.Prime 239890093 := by
  apply lucas_primality 239890093 (5 : ZMod 239890093)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (23, 1), (37, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (23, 1), (37, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) = 239890093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_37
      · exact prime_ninetySevenCQ_139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 239890093) ^ 119945046 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 239890093) ^ 79963364 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 239890093) ^ 18453084 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 239890093) ^ 10430004 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 239890093) ^ 6483516 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 239890093) ^ 1725828 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_248777147 : Nat.Prime 248777147 := by
  apply lucas_primality 248777147 (2 : ZMod 248777147)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (6546767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (6546767, 1)] : List FactorBlock).map factorBlockValue).prod) = 248777147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_6546767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 248777147) ^ 124388573 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 248777147) ^ 13093534 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 248777147) ^ 38 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_255459179 : Nat.Prime 255459179 := by
  apply lucas_primality 255459179 (2 : ZMod 255459179)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (397, 1), (24749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (397, 1), (24749, 1)] : List FactorBlock).map factorBlockValue).prod) = 255459179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_397
      · exact prime_ninetySevenCQ_24749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 255459179) ^ 127729589 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 255459179) ^ 19650706 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 255459179) ^ 643474 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 255459179) ^ 10322 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_286306261 : Nat.Prime 286306261 := by
  apply lucas_primality 286306261 (6 : ZMod 286306261)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (127, 1), (37573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (127, 1), (37573, 1)] : List FactorBlock).map factorBlockValue).prod) = 286306261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_127
      · exact prime_ninetySevenCQ_37573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 286306261) ^ 143153130 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 286306261) ^ 95435420 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 286306261) ^ 57261252 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 286306261) ^ 2254380 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 286306261) ^ 7620 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_305262127 : Nat.Prime 305262127 := by
  apply lucas_primality 305262127 (3 : ZMod 305262127)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1304539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1304539, 1)] : List FactorBlock).map factorBlockValue).prod) = 305262127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_1304539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 305262127) ^ 152631063 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 305262127) ^ 101754042 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 305262127) ^ 23481702 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 305262127) ^ 234 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_313768361 : Nat.Prime 313768361 := by
  apply lucas_primality 313768361 (6 : ZMod 313768361)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (31, 1), (137, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (31, 1), (137, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) = 313768361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_137
      · exact prime_ninetySevenCQ_1847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 313768361) ^ 156884180 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 313768361) ^ 62753672 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 313768361) ^ 10121560 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 313768361) ^ 2290280 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 313768361) ^ 169880 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_322386919 : Nat.Prime 322386919 := by
  apply lucas_primality 322386919 (6 : ZMod 322386919)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (31, 1), (247609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (31, 1), (247609, 1)] : List FactorBlock).map factorBlockValue).prod) = 322386919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_247609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 322386919) ^ 161193459 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 322386919) ^ 107462306 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 322386919) ^ 46055274 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 322386919) ^ 10399578 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 322386919) ^ 1302 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_322633781 : Nat.Prime 322633781 := by
  apply lucas_primality 322633781 (2 : ZMod 322633781)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (2304527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (2304527, 1)] : List FactorBlock).map factorBlockValue).prod) = 322633781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_2304527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 322633781) ^ 161316890 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 322633781) ^ 64526756 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 322633781) ^ 46090540 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 322633781) ^ 140 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_353278829 : Nat.Prime 353278829 := by
  apply lucas_primality 353278829 (2 : ZMod 353278829)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (73, 1), (24691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (73, 1), (24691, 1)] : List FactorBlock).map factorBlockValue).prod) = 353278829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_73
      · exact prime_ninetySevenCQ_24691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 353278829) ^ 176639414 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 353278829) ^ 50468404 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 353278829) ^ 4839436 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 353278829) ^ 14308 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_357907813 : Nat.Prime 357907813 := by
  apply lucas_primality 357907813 (2 : ZMod 357907813)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29825651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29825651, 1)] : List FactorBlock).map factorBlockValue).prod) = 357907813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_29825651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 357907813) ^ 178953906 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 357907813) ^ 119302604 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 357907813) ^ 12 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_400870487 : Nat.Prime 400870487 := by
  apply lucas_primality 400870487 (5 : ZMod 400870487)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (6465653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (6465653, 1)] : List FactorBlock).map factorBlockValue).prod) = 400870487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_6465653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 400870487) ^ 200435243 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 400870487) ^ 12931306 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 400870487) ^ 62 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_420213173 : Nat.Prime 420213173 := by
  apply lucas_primality 420213173 (2 : ZMod 420213173)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (223, 1), (471091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (223, 1), (471091, 1)] : List FactorBlock).map factorBlockValue).prod) = 420213173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_223
      · exact prime_ninetySevenCQ_471091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 420213173) ^ 210106586 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 420213173) ^ 1884364 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 420213173) ^ 892 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_463150607 : Nat.Prime 463150607 := by
  apply lucas_primality 463150607 (5 : ZMod 463150607)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (231575303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (231575303, 1)] : List FactorBlock).map factorBlockValue).prod) = 463150607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_231575303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 463150607) ^ 231575303 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 463150607) ^ 2 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_490680539 : Nat.Prime 490680539 := by
  apply lucas_primality 490680539 (2 : ZMod 490680539)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 2), (145949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 2), (145949, 1)] : List FactorBlock).map factorBlockValue).prod) = 490680539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_41
      · exact prime_ninetySevenCQ_145949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 490680539) ^ 245340269 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 490680539) ^ 11967818 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 490680539) ^ 3362 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_525340813 : Nat.Prime 525340813 := by
  apply lucas_primality 525340813 (2 : ZMod 525340813)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (769, 1), (56929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (769, 1), (56929, 1)] : List FactorBlock).map factorBlockValue).prod) = 525340813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_769
      · exact prime_ninetySevenCQ_56929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 525340813) ^ 262670406 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 525340813) ^ 175113604 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 525340813) ^ 683148 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 525340813) ^ 9228 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_530805823 : Nat.Prime 530805823 := by
  apply lucas_primality 530805823 (5 : ZMod 530805823)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1907, 1), (2017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1907, 1), (2017, 1)] : List FactorBlock).map factorBlockValue).prod) = 530805823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_1907
      · exact prime_ninetySevenCQ_2017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 530805823) ^ 265402911 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 530805823) ^ 176935274 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 530805823) ^ 23078514 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 530805823) ^ 278346 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 530805823) ^ 263166 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_532708361 : Nat.Prime 532708361 := by
  apply lucas_primality 532708361 (6 : ZMod 532708361)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13317709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13317709, 1)] : List FactorBlock).map factorBlockValue).prod) = 532708361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_13317709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 532708361) ^ 266354180 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 532708361) ^ 106541672 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 532708361) ^ 40 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_548739043 : Nat.Prime 548739043 := by
  apply lucas_primality 548739043 (2 : ZMod 548739043)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (1499287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (1499287, 1)] : List FactorBlock).map factorBlockValue).prod) = 548739043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_61
      · exact prime_ninetySevenCQ_1499287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 548739043) ^ 274369521 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 548739043) ^ 182913014 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 548739043) ^ 8995722 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 548739043) ^ 366 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_578854069 : Nat.Prime 578854069 := by
  apply lucas_primality 578854069 (7 : ZMod 578854069)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (47, 1), (6073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (47, 1), (6073, 1)] : List FactorBlock).map factorBlockValue).prod) = 578854069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_47
      · exact prime_ninetySevenCQ_6073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 578854069) ^ 289427034 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 578854069) ^ 192951356 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 578854069) ^ 44527236 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 578854069) ^ 12316044 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 578854069) ^ 95316 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_645267563 : Nat.Prime 645267563 := by
  apply lucas_primality 645267563 (2 : ZMod 645267563)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (322633781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (322633781, 1)] : List FactorBlock).map factorBlockValue).prod) = 645267563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_322633781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 645267563) ^ 322633781 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 645267563) ^ 2 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_689174281 : Nat.Prime 689174281 := by
  apply lucas_primality 689174281 (14 : ZMod 689174281)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (59, 1), (71, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (59, 1), (71, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) = 689174281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_59
      · exact prime_ninetySevenCQ_71
      · exact prime_ninetySevenCQ_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 689174281) ^ 344587140 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (14 : ZMod 689174281) ^ 229724760 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (14 : ZMod 689174281) ^ 137834856 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (14 : ZMod 689174281) ^ 11680920 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (14 : ZMod 689174281) ^ 9706680 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (14 : ZMod 689174281) ^ 1508040 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_721637507 : Nat.Prime 721637507 := by
  apply lucas_primality 721637507 (2 : ZMod 721637507)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (6807901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (6807901, 1)] : List FactorBlock).map factorBlockValue).prod) = 721637507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_53
      · exact prime_ninetySevenCQ_6807901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 721637507) ^ 360818753 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 721637507) ^ 13615802 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 721637507) ^ 106 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_744576457 : Nat.Prime 744576457 := by
  apply lucas_primality 744576457 (10 : ZMod 744576457)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (37, 1), (64499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (37, 1), (64499, 1)] : List FactorBlock).map factorBlockValue).prod) = 744576457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_37
      · exact prime_ninetySevenCQ_64499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 744576457) ^ 372288228 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 744576457) ^ 248192152 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 744576457) ^ 57275112 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 744576457) ^ 20123688 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 744576457) ^ 11544 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_822790961 : Nat.Prime 822790961 := by
  apply lucas_primality 822790961 (6 : ZMod 822790961)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (23, 1), (239, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (23, 1), (239, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) = 822790961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_239
      · exact prime_ninetySevenCQ_1871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 822790961) ^ 411395480 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 822790961) ^ 164558192 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 822790961) ^ 35773520 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 822790961) ^ 3442640 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 822790961) ^ 439760 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_843247849 : Nat.Prime 843247849 := by
  apply lucas_primality 843247849 (7 : ZMod 843247849)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (1211563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (1211563, 1)] : List FactorBlock).map factorBlockValue).prod) = 843247849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_29
      · exact prime_ninetySevenCQ_1211563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 843247849) ^ 421623924 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 843247849) ^ 281082616 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 843247849) ^ 29077512 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 843247849) ^ 696 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_886517161 : Nat.Prime 886517161 := by
  apply lucas_primality 886517161 (7 : ZMod 886517161)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7387643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7387643, 1)] : List FactorBlock).map factorBlockValue).prod) = 886517161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7387643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 886517161) ^ 443258580 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 886517161) ^ 295505720 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 886517161) ^ 177303432 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 886517161) ^ 120 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1513146007 : Nat.Prime 1513146007 := by
  apply lucas_primality 1513146007 (3 : ZMod 1513146007)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (43, 1), (52837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (43, 1), (52837, 1)] : List FactorBlock).map factorBlockValue).prod) = 1513146007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_37
      · exact prime_ninetySevenCQ_43
      · exact prime_ninetySevenCQ_52837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1513146007) ^ 756573003 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1513146007) ^ 504382002 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1513146007) ^ 40895838 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1513146007) ^ 35189442 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1513146007) ^ 28638 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1679964029 : Nat.Prime 1679964029 := by
  apply lucas_primality 1679964029 (2 : ZMod 1679964029)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (1789, 1), (7573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (1789, 1), (7573, 1)] : List FactorBlock).map factorBlockValue).prod) = 1679964029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_1789
      · exact prime_ninetySevenCQ_7573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1679964029) ^ 839982014 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679964029) ^ 54192388 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679964029) ^ 939052 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679964029) ^ 221836 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1903552247 : Nat.Prime 1903552247 := by
  apply lucas_primality 1903552247 (5 : ZMod 1903552247)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (25723679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (25723679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1903552247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_37
      · exact prime_ninetySevenCQ_25723679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1903552247) ^ 951776123 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1903552247) ^ 51447358 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1903552247) ^ 74 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2629987891 : Nat.Prime 2629987891 := by
  apply lucas_primality 2629987891 (3 : ZMod 2629987891)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (5156839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (5156839, 1)] : List FactorBlock).map factorBlockValue).prod) = 2629987891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_5156839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2629987891) ^ 1314993945 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2629987891) ^ 876662630 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2629987891) ^ 525997578 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2629987891) ^ 154705170 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2629987891) ^ 510 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2695418723 : Nat.Prime 2695418723 := by
  apply lucas_primality 2695418723 (5 : ZMod 2695418723)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (631, 1), (2135831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (631, 1), (2135831, 1)] : List FactorBlock).map factorBlockValue).prod) = 2695418723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_631
      · exact prime_ninetySevenCQ_2135831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2695418723) ^ 1347709361 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2695418723) ^ 4271662 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2695418723) ^ 1262 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2705515121 : Nat.Prime 2705515121 := by
  apply lucas_primality 2705515121 (3 : ZMod 2705515121)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (11, 1), (293, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (11, 1), (293, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) = 2705515121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_293
      · exact prime_ninetySevenCQ_1499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2705515121) ^ 1352757560 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2705515121) ^ 541103024 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2705515121) ^ 386502160 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2705515121) ^ 245955920 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2705515121) ^ 9233840 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2705515121) ^ 1804880 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_3270900859 : Nat.Prime 3270900859 := by
  apply lucas_primality 3270900859 (3 : ZMod 3270900859)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (21499, 1), (25357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (21499, 1), (25357, 1)] : List FactorBlock).map factorBlockValue).prod) = 3270900859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_21499
      · exact prime_ninetySevenCQ_25357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3270900859) ^ 1635450429 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3270900859) ^ 1090300286 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3270900859) ^ 152142 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3270900859) ^ 128994 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_3271723307 : Nat.Prime 3271723307 := by
  apply lucas_primality 3271723307 (2 : ZMod 3271723307)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (227, 1), (691, 1), (10429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (227, 1), (691, 1), (10429, 1)] : List FactorBlock).map factorBlockValue).prod) = 3271723307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_227
      · exact prime_ninetySevenCQ_691
      · exact prime_ninetySevenCQ_10429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3271723307) ^ 1635861653 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3271723307) ^ 14412878 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3271723307) ^ 4734766 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3271723307) ^ 313714 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_3299797243 : Nat.Prime 3299797243 := by
  apply lucas_primality 3299797243 (7 : ZMod 3299797243)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (26188867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (26188867, 1)] : List FactorBlock).map factorBlockValue).prod) = 3299797243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_26188867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3299797243) ^ 1649898621 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3299797243) ^ 1099932414 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3299797243) ^ 471399606 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3299797243) ^ 126 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_4267783123 : Nat.Prime 4267783123 := by
  apply lucas_primality 4267783123 (5 : ZMod 4267783123)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (991, 1), (42221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (991, 1), (42221, 1)] : List FactorBlock).map factorBlockValue).prod) = 4267783123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_991
      · exact prime_ninetySevenCQ_42221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4267783123) ^ 2133891561 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4267783123) ^ 1422594374 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4267783123) ^ 251046066 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4267783123) ^ 4306542 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4267783123) ^ 101082 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_4490411789 : Nat.Prime 4490411789 := by
  apply lucas_primality 4490411789 (3 : ZMod 4490411789)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (18403327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (18403327, 1)] : List FactorBlock).map factorBlockValue).prod) = 4490411789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_61
      · exact prime_ninetySevenCQ_18403327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4490411789) ^ 2245205894 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4490411789) ^ 73613308 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4490411789) ^ 244 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_4863559817 : Nat.Prime 4863559817 := by
  apply lucas_primality 4863559817 (3 : ZMod 4863559817)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (157, 1), (311, 1), (12451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (157, 1), (311, 1), (12451, 1)] : List FactorBlock).map factorBlockValue).prod) = 4863559817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_157
      · exact prime_ninetySevenCQ_311
      · exact prime_ninetySevenCQ_12451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4863559817) ^ 2431779908 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4863559817) ^ 30978088 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4863559817) ^ 15638456 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4863559817) ^ 390616 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_4936745767 : Nat.Prime 4936745767 := by
  apply lucas_primality 4936745767 (5 : ZMod 4936745767)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (822790961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (822790961, 1)] : List FactorBlock).map factorBlockValue).prod) = 4936745767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_822790961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4936745767) ^ 2468372883 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4936745767) ^ 1645581922 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4936745767) ^ 6 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_4956924737 : Nat.Prime 4956924737 := by
  apply lucas_primality 4956924737 (3 : ZMod 4956924737)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (17, 1), (4555997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (17, 1), (4555997, 1)] : List FactorBlock).map factorBlockValue).prod) = 4956924737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_4555997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4956924737) ^ 2478462368 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4956924737) ^ 291583808 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4956924737) ^ 1088 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_5126961097 : Nat.Prime 5126961097 := by
  apply lucas_primality 5126961097 (7 : ZMod 5126961097)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (23, 1), (419, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (23, 1), (419, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) = 5126961097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_419
      · exact prime_ninetySevenCQ_821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5126961097) ^ 2563480548 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126961097) ^ 1708987032 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126961097) ^ 222911352 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126961097) ^ 12236184 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5126961097) ^ 6244776 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_6201093391 : Nat.Prime 6201093391 := by
  apply lucas_primality 6201093391 (6 : ZMod 6201093391)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (206703113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (206703113, 1)] : List FactorBlock).map factorBlockValue).prod) = 6201093391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_206703113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6201093391) ^ 3100546695 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 6201093391) ^ 2067031130 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 6201093391) ^ 1240218678 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 6201093391) ^ 30 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_7199768747 : Nat.Prime 7199768747 := by
  apply lucas_primality 7199768747 (2 : ZMod 7199768747)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (659, 1), (5462647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (659, 1), (5462647, 1)] : List FactorBlock).map factorBlockValue).prod) = 7199768747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_659
      · exact prime_ninetySevenCQ_5462647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7199768747) ^ 3599884373 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7199768747) ^ 10925294 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7199768747) ^ 1318 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_7254044009 : Nat.Prime 7254044009 := by
  apply lucas_primality 7254044009 (3 : ZMod 7254044009)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (191, 1), (1861, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (191, 1), (1861, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) = 7254044009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_191
      · exact prime_ninetySevenCQ_1861
      · exact prime_ninetySevenCQ_2551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7254044009) ^ 3627022004 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7254044009) ^ 37979288 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7254044009) ^ 3897928 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7254044009) ^ 2843608 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_8250619691 : Nat.Prime 8250619691 := by
  apply lucas_primality 8250619691 (2 : ZMod 8250619691)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (2621, 1), (18517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (2621, 1), (18517, 1)] : List FactorBlock).map factorBlockValue).prod) = 8250619691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_2621
      · exact prime_ninetySevenCQ_18517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8250619691) ^ 4125309845 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8250619691) ^ 1650123938 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8250619691) ^ 485330570 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8250619691) ^ 3147890 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8250619691) ^ 445570 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_9042498151 : Nat.Prime 9042498151 := by
  apply lucas_primality 9042498151 (7 : ZMod 9042498151)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (8611903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (8611903, 1)] : List FactorBlock).map factorBlockValue).prod) = 9042498151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_8611903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 9042498151) ^ 4521249075 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 9042498151) ^ 3014166050 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 9042498151) ^ 1808499630 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 9042498151) ^ 1291785450 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 9042498151) ^ 1050 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_9083804699 : Nat.Prime 9083804699 := by
  apply lucas_primality 9083804699 (2 : ZMod 9083804699)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (146512979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (146512979, 1)] : List FactorBlock).map factorBlockValue).prod) = 9083804699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_146512979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9083804699) ^ 4541902349 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9083804699) ^ 293025958 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9083804699) ^ 62 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_10013216443 : Nat.Prime 10013216443 := by
  apply lucas_primality 10013216443 (2 : ZMod 10013216443)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (53834497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (53834497, 1)] : List FactorBlock).map factorBlockValue).prod) = 10013216443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_53834497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10013216443) ^ 5006608221 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10013216443) ^ 3337738814 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10013216443) ^ 323006982 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10013216443) ^ 186 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_10126690367 : Nat.Prime 10126690367 := by
  apply lucas_primality 10126690367 (10 : ZMod 10126690367)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (79, 1), (1091, 1), (4519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (79, 1), (1091, 1), (4519, 1)] : List FactorBlock).map factorBlockValue).prod) = 10126690367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_79
      · exact prime_ninetySevenCQ_1091
      · exact prime_ninetySevenCQ_4519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10126690367) ^ 5063345183 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 10126690367) ^ 778976182 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 10126690367) ^ 128185954 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 10126690367) ^ 9282026 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 10126690367) ^ 2240914 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_11600451613 : Nat.Prime 11600451613 := by
  apply lucas_primality 11600451613 (5 : ZMod 11600451613)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 9), (147341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 9), (147341, 1)] : List FactorBlock).map factorBlockValue).prod) = 11600451613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_147341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11600451613) ^ 5800225806 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11600451613) ^ 3866817204 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11600451613) ^ 78732 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_11706188987 : Nat.Prime 11706188987 := by
  apply lucas_primality 11706188987 (2 : ZMod 11706188987)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1409, 1), (4154077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1409, 1), (4154077, 1)] : List FactorBlock).map factorBlockValue).prod) = 11706188987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_1409
      · exact prime_ninetySevenCQ_4154077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11706188987) ^ 5853094493 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11706188987) ^ 8308154 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11706188987) ^ 2818 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_13794795667 : Nat.Prime 13794795667 := by
  apply lucas_primality 13794795667 (2 : ZMod 13794795667)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (255459179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (255459179, 1)] : List FactorBlock).map factorBlockValue).prod) = 13794795667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_255459179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13794795667) ^ 6897397833 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13794795667) ^ 4598265222 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13794795667) ^ 54 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_13876011319 : Nat.Prime 13876011319 := by
  apply lucas_primality 13876011319 (3 : ZMod 13876011319)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (223, 1), (797747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (223, 1), (797747, 1)] : List FactorBlock).map factorBlockValue).prod) = 13876011319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_223
      · exact prime_ninetySevenCQ_797747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13876011319) ^ 6938005659 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13876011319) ^ 4625337106 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13876011319) ^ 1067385486 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13876011319) ^ 62224266 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13876011319) ^ 17394 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_15557491601 : Nat.Prime 15557491601 := by
  apply lucas_primality 15557491601 (3 : ZMod 15557491601)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (7, 1), (71, 1), (139, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (7, 1), (71, 1), (139, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod) = 15557491601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_71
      · exact prime_ninetySevenCQ_139
      · exact prime_ninetySevenCQ_563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15557491601) ^ 7778745800 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 15557491601) ^ 3111498320 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 15557491601) ^ 2222498800 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 15557491601) ^ 219119600 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 15557491601) ^ 111924400 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 15557491601) ^ 27633200 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_16290864229 : Nat.Prime 16290864229 := by
  apply lucas_primality 16290864229 (2 : ZMod 16290864229)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (1217, 1), (18287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (1217, 1), (18287, 1)] : List FactorBlock).map factorBlockValue).prod) = 16290864229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_61
      · exact prime_ninetySevenCQ_1217
      · exact prime_ninetySevenCQ_18287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16290864229) ^ 8145432114 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16290864229) ^ 5430288076 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16290864229) ^ 267063348 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16290864229) ^ 13386084 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16290864229) ^ 890844 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_16806211171 : Nat.Prime 16806211171 := by
  apply lucas_primality 16806211171 (7 : ZMod 16806211171)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (163, 1), (25841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (163, 1), (25841, 1)] : List FactorBlock).map factorBlockValue).prod) = 16806211171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_163
      · exact prime_ninetySevenCQ_25841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16806211171) ^ 8403105585 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16806211171) ^ 5602070390 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16806211171) ^ 3361242234 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16806211171) ^ 2400887310 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16806211171) ^ 884537430 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16806211171) ^ 103105590 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16806211171) ^ 650370 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_18714988727 : Nat.Prime 18714988727 := by
  apply lucas_primality 18714988727 (5 : ZMod 18714988727)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (823, 1), (70621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (823, 1), (70621, 1)] : List FactorBlock).map factorBlockValue).prod) = 18714988727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_823
      · exact prime_ninetySevenCQ_70621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18714988727) ^ 9357494363 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 18714988727) ^ 2673569818 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 18714988727) ^ 813695162 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 18714988727) ^ 22739962 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 18714988727) ^ 265006 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_19971689923 : Nat.Prime 19971689923 := by
  apply lucas_primality 19971689923 (3 : ZMod 19971689923)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (35791559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (35791559, 1)] : List FactorBlock).map factorBlockValue).prod) = 19971689923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_35791559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 19971689923) ^ 9985844961 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 19971689923) ^ 6657229974 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 19971689923) ^ 644248062 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 19971689923) ^ 558 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_21882399673 : Nat.Prime 21882399673 := by
  apply lucas_primality 21882399673 (5 : ZMod 21882399673)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (130252379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (130252379, 1)] : List FactorBlock).map factorBlockValue).prod) = 21882399673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_130252379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21882399673) ^ 10941199836 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21882399673) ^ 7294133224 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21882399673) ^ 3126057096 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21882399673) ^ 168 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_22834641337 : Nat.Prime 22834641337 := by
  apply lucas_primality 22834641337 (11 : ZMod 22834641337)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (113, 1), (191, 1), (3391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (113, 1), (191, 1), (3391, 1)] : List FactorBlock).map factorBlockValue).prod) = 22834641337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_113
      · exact prime_ninetySevenCQ_191
      · exact prime_ninetySevenCQ_3391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 22834641337) ^ 11417320668 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 22834641337) ^ 7611547112 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 22834641337) ^ 1756510872 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 22834641337) ^ 202076472 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 22834641337) ^ 119553096 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 22834641337) ^ 6733896 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_25774089239 : Nat.Prime 25774089239 := by
  apply lucas_primality 25774089239 (13 : ZMod 25774089239)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1013, 1), (12721663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1013, 1), (12721663, 1)] : List FactorBlock).map factorBlockValue).prod) = 25774089239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_1013
      · exact prime_ninetySevenCQ_12721663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 25774089239) ^ 12887044619 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 25774089239) ^ 25443326 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 25774089239) ^ 2026 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_25857043243 : Nat.Prime 25857043243 := by
  apply lucas_primality 25857043243 (2 : ZMod 25857043243)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (62171, 1), (69317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (62171, 1), (69317, 1)] : List FactorBlock).map factorBlockValue).prod) = 25857043243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_62171
      · exact prime_ninetySevenCQ_69317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25857043243) ^ 12928521621 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25857043243) ^ 8619014414 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25857043243) ^ 415902 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25857043243) ^ 373026 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_29955141583 : Nat.Prime 29955141583 := by
  apply lucas_primality 29955141583 (5 : ZMod 29955141583)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (191, 1), (26138867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (191, 1), (26138867, 1)] : List FactorBlock).map factorBlockValue).prod) = 29955141583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_191
      · exact prime_ninetySevenCQ_26138867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29955141583) ^ 14977570791 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 29955141583) ^ 9985047194 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 29955141583) ^ 156833202 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 29955141583) ^ 1146 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_32058614251 : Nat.Prime 32058614251 := by
  apply lucas_primality 32058614251 (2 : ZMod 32058614251)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (13, 1), (167, 1), (6563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (13, 1), (167, 1), (6563, 1)] : List FactorBlock).map factorBlockValue).prod) = 32058614251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_167
      · exact prime_ninetySevenCQ_6563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32058614251) ^ 16029307125 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32058614251) ^ 10686204750 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32058614251) ^ 6411722850 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32058614251) ^ 2466047250 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32058614251) ^ 191967750 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 32058614251) ^ 4884750 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_33511045433 : Nat.Prime 33511045433 := by
  apply lucas_primality 33511045433 (3 : ZMod 33511045433)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (26921, 1), (155599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (26921, 1), (155599, 1)] : List FactorBlock).map factorBlockValue).prod) = 33511045433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_26921
      · exact prime_ninetySevenCQ_155599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33511045433) ^ 16755522716 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33511045433) ^ 1244792 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33511045433) ^ 215368 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_41416074017 : Nat.Prime 41416074017 := by
  apply lucas_primality 41416074017 (3 : ZMod 41416074017)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (43, 1), (311, 1), (5693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (43, 1), (311, 1), (5693, 1)] : List FactorBlock).map factorBlockValue).prod) = 41416074017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_43
      · exact prime_ninetySevenCQ_311
      · exact prime_ninetySevenCQ_5693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41416074017) ^ 20708037008 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 41416074017) ^ 2436239648 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 41416074017) ^ 963164512 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 41416074017) ^ 133170656 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 41416074017) ^ 7274912 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_44811718433 : Nat.Prime 44811718433 := by
  apply lucas_primality 44811718433 (3 : ZMod 44811718433)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (23, 1), (4683499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (23, 1), (4683499, 1)] : List FactorBlock).map factorBlockValue).prod) = 44811718433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_4683499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 44811718433) ^ 22405859216 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44811718433) ^ 3447055264 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44811718433) ^ 1948335584 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44811718433) ^ 9568 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_45056730713 : Nat.Prime 45056730713 := by
  apply lucas_primality 45056730713 (3 : ZMod 45056730713)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (26267, 1), (30631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (26267, 1), (30631, 1)] : List FactorBlock).map factorBlockValue).prod) = 45056730713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_26267
      · exact prime_ninetySevenCQ_30631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45056730713) ^ 22528365356 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 45056730713) ^ 6436675816 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 45056730713) ^ 1715336 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 45056730713) ^ 1470952 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_48731389363 : Nat.Prime 48731389363 := by
  apply lucas_primality 48731389363 (2 : ZMod 48731389363)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 2), (2817169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 2), (2817169, 1)] : List FactorBlock).map factorBlockValue).prod) = 48731389363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_2817169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48731389363) ^ 24365694681 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 48731389363) ^ 16243796454 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 48731389363) ^ 1571980302 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 48731389363) ^ 17298 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_58845392273 : Nat.Prime 58845392273 := by
  apply lucas_primality 58845392273 (3 : ZMod 58845392273)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (73, 1), (509, 1), (98981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (73, 1), (509, 1), (98981, 1)] : List FactorBlock).map factorBlockValue).prod) = 58845392273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_73
      · exact prime_ninetySevenCQ_509
      · exact prime_ninetySevenCQ_98981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 58845392273) ^ 29422696136 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58845392273) ^ 806101264 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58845392273) ^ 115609808 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58845392273) ^ 594512 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_69460137797 : Nat.Prime 69460137797 := by
  apply lucas_primality 69460137797 (2 : ZMod 69460137797)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (571, 1), (4344517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (571, 1), (4344517, 1)] : List FactorBlock).map factorBlockValue).prod) = 69460137797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_571
      · exact prime_ninetySevenCQ_4344517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69460137797) ^ 34730068898 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 69460137797) ^ 9922876828 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 69460137797) ^ 121646476 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 69460137797) ^ 15988 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_71348922109 : Nat.Prime 71348922109 := by
  apply lucas_primality 71348922109 (6 : ZMod 71348922109)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (21803, 1), (90901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (21803, 1), (90901, 1)] : List FactorBlock).map factorBlockValue).prod) = 71348922109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_21803
      · exact prime_ninetySevenCQ_90901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 71348922109) ^ 35674461054 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 71348922109) ^ 23782974036 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 71348922109) ^ 3272436 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 71348922109) ^ 784908 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_91942439081 : Nat.Prime 91942439081 := by
  apply lucas_primality 91942439081 (3 : ZMod 91942439081)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (131, 1), (317, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (131, 1), (317, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) = 91942439081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_131
      · exact prime_ninetySevenCQ_317
      · exact prime_ninetySevenCQ_55351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 91942439081) ^ 45971219540 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 91942439081) ^ 18388487816 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 91942439081) ^ 701850680 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 91942439081) ^ 290039240 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 91942439081) ^ 1661080 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_104685326747 : Nat.Prime 104685326747 := by
  apply lucas_primality 104685326747 (2 : ZMod 104685326747)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (13, 1), (797, 1), (65609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (13, 1), (797, 1), (65609, 1)] : List FactorBlock).map factorBlockValue).prod) = 104685326747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_797
      · exact prime_ninetySevenCQ_65609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104685326747) ^ 52342663373 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 104685326747) ^ 14955046678 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 104685326747) ^ 9516847886 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 104685326747) ^ 8052717442 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 104685326747) ^ 131349218 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 104685326747) ^ 1595594 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_144895871657 : Nat.Prime 144895871657 := by
  apply lucas_primality 144895871657 (3 : ZMod 144895871657)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (31, 1), (223, 1), (229, 1), (673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (31, 1), (223, 1), (229, 1), (673, 1)] : List FactorBlock).map factorBlockValue).prod) = 144895871657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_223
      · exact prime_ninetySevenCQ_229
      · exact prime_ninetySevenCQ_673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 144895871657) ^ 72447935828 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 144895871657) ^ 8523286568 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 144895871657) ^ 4674060376 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 144895871657) ^ 649757272 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 144895871657) ^ 632733064 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 144895871657) ^ 215298472 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_150782672351 : Nat.Prime 150782672351 := by
  apply lucas_primality 150782672351 (11 : ZMod 150782672351)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2999, 1), (1005553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2999, 1), (1005553, 1)] : List FactorBlock).map factorBlockValue).prod) = 150782672351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_2999
      · exact prime_ninetySevenCQ_1005553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 150782672351) ^ 75391336175 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 150782672351) ^ 30156534470 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 150782672351) ^ 50277650 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 150782672351) ^ 149950 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_152749168259 : Nat.Prime 152749168259 := by
  apply lucas_primality 152749168259 (2 : ZMod 152749168259)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (248777147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (248777147, 1)] : List FactorBlock).map factorBlockValue).prod) = 152749168259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_307
      · exact prime_ninetySevenCQ_248777147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 152749168259) ^ 76374584129 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 152749168259) ^ 497554294 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 152749168259) ^ 614 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_179246891167 : Nat.Prime 179246891167 := by
  apply lucas_primality 179246891167 (3 : ZMod 179246891167)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (4267783123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (4267783123, 1)] : List FactorBlock).map factorBlockValue).prod) = 179246891167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_4267783123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 179246891167) ^ 89623445583 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 179246891167) ^ 59748963722 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 179246891167) ^ 25606698738 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 179246891167) ^ 42 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_198325873871 : Nat.Prime 198325873871 := by
  apply lucas_primality 198325873871 (11 : ZMod 198325873871)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (109, 1), (313, 1), (581311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (109, 1), (313, 1), (581311, 1)] : List FactorBlock).map factorBlockValue).prod) = 198325873871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_109
      · exact prime_ninetySevenCQ_313
      · exact prime_ninetySevenCQ_581311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 198325873871) ^ 99162936935 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 198325873871) ^ 39665174774 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 198325873871) ^ 1819503430 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 198325873871) ^ 633628990 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 198325873871) ^ 341170 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_218823996731 : Nat.Prime 218823996731 := by
  apply lucas_primality 218823996731 (2 : ZMod 218823996731)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (21882399673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (21882399673, 1)] : List FactorBlock).map factorBlockValue).prod) = 218823996731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_21882399673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 218823996731) ^ 109411998365 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 218823996731) ^ 43764799346 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 218823996731) ^ 10 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_236437255643 : Nat.Prime 236437255643 := by
  apply lucas_primality 236437255643 (2 : ZMod 236437255643)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (89, 1), (189757027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (89, 1), (189757027, 1)] : List FactorBlock).map factorBlockValue).prod) = 236437255643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_89
      · exact prime_ninetySevenCQ_189757027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 236437255643) ^ 118218627821 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 236437255643) ^ 33776750806 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 236437255643) ^ 2656598378 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 236437255643) ^ 1246 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_250763793263 : Nat.Prime 250763793263 := by
  apply lucas_primality 250763793263 (5 : ZMod 250763793263)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149183, 1), (840457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149183, 1), (840457, 1)] : List FactorBlock).map factorBlockValue).prod) = 250763793263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_149183
      · exact prime_ninetySevenCQ_840457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 250763793263) ^ 125381896631 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 250763793263) ^ 1680914 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 250763793263) ^ 298366 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_293436947863 : Nat.Prime 293436947863 := by
  apply lucas_primality 293436947863 (3 : ZMod 293436947863)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (83, 1), (89, 1), (163, 1), (4513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (83, 1), (89, 1), (163, 1), (4513, 1)] : List FactorBlock).map factorBlockValue).prod) = 293436947863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_83
      · exact prime_ninetySevenCQ_89
      · exact prime_ninetySevenCQ_163
      · exact prime_ninetySevenCQ_4513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 293436947863) ^ 146718473931 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 293436947863) ^ 97812315954 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 293436947863) ^ 3535384914 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 293436947863) ^ 3297044358 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 293436947863) ^ 1800226674 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 293436947863) ^ 65020374 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_328453148141 : Nat.Prime 328453148141 := by
  apply lucas_primality 328453148141 (2 : ZMod 328453148141)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (17, 1), (131, 1), (567257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (17, 1), (131, 1), (567257, 1)] : List FactorBlock).map factorBlockValue).prod) = 328453148141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_131
      · exact prime_ninetySevenCQ_567257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 328453148141) ^ 164226574070 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 328453148141) ^ 65690629628 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 328453148141) ^ 25265626780 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 328453148141) ^ 19320773420 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 328453148141) ^ 2507275940 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 328453148141) ^ 579020 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_361699001689 : Nat.Prime 361699001689 := by
  apply lucas_primality 361699001689 (29 : ZMod 361699001689)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (886517161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (886517161, 1)] : List FactorBlock).map factorBlockValue).prod) = 361699001689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_886517161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 361699001689) ^ 180849500844 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (29 : ZMod 361699001689) ^ 120566333896 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (29 : ZMod 361699001689) ^ 21276411864 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (29 : ZMod 361699001689) ^ 408 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_406292139733 : Nat.Prime 406292139733 := by
  apply lucas_primality 406292139733 (5 : ZMod 406292139733)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (12953, 1), (137573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (12953, 1), (137573, 1)] : List FactorBlock).map factorBlockValue).prod) = 406292139733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_12953
      · exact prime_ninetySevenCQ_137573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 406292139733) ^ 203146069866 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 406292139733) ^ 135430713244 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 406292139733) ^ 21383796828 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 406292139733) ^ 31366644 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 406292139733) ^ 2953284 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_418764254401 : Nat.Prime 418764254401 := by
  apply lucas_primality 418764254401 (14 : ZMod 418764254401)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (599, 1), (16183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (599, 1), (16183, 1)] : List FactorBlock).map factorBlockValue).prod) = 418764254401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_599
      · exact prime_ninetySevenCQ_16183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 418764254401) ^ 209382127200 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (14 : ZMod 418764254401) ^ 139588084800 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (14 : ZMod 418764254401) ^ 83752850880 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (14 : ZMod 418764254401) ^ 699105600 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (14 : ZMod 418764254401) ^ 25876800 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_437647993463 : Nat.Prime 437647993463 := by
  apply lucas_primality 437647993463 (5 : ZMod 437647993463)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (218823996731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (218823996731, 1)] : List FactorBlock).map factorBlockValue).prod) = 437647993463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_218823996731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 437647993463) ^ 218823996731 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 437647993463) ^ 2 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_444275901467 : Nat.Prime 444275901467 := by
  apply lucas_primality 444275901467 (2 : ZMod 444275901467)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (9551, 1), (1011221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (9551, 1), (1011221, 1)] : List FactorBlock).map factorBlockValue).prod) = 444275901467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_9551
      · exact prime_ninetySevenCQ_1011221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 444275901467) ^ 222137950733 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 444275901467) ^ 19316343542 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 444275901467) ^ 46516166 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 444275901467) ^ 439346 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_449159729449 : Nat.Prime 449159729449 := by
  apply lucas_primality 449159729449 (11 : ZMod 449159729449)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (18714988727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (18714988727, 1)] : List FactorBlock).map factorBlockValue).prod) = 449159729449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_18714988727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 449159729449) ^ 224579864724 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 449159729449) ^ 149719909816 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 449159729449) ^ 24 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_704978541859 : Nat.Prime 704978541859 := by
  apply lucas_primality 704978541859 (2 : ZMod 704978541859)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1367, 1), (4523791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1367, 1), (4523791, 1)] : List FactorBlock).map factorBlockValue).prod) = 704978541859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_1367
      · exact prime_ninetySevenCQ_4523791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 704978541859) ^ 352489270929 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 704978541859) ^ 234992847286 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 704978541859) ^ 37104133782 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 704978541859) ^ 515712174 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 704978541859) ^ 155838 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_826978418381 : Nat.Prime 826978418381 := by
  apply lucas_primality 826978418381 (2 : ZMod 826978418381)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17483, 1), (2365093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17483, 1), (2365093, 1)] : List FactorBlock).map factorBlockValue).prod) = 826978418381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_17483
      · exact prime_ninetySevenCQ_2365093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 826978418381) ^ 413489209190 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 826978418381) ^ 165395683676 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 826978418381) ^ 47301860 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 826978418381) ^ 349660 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_906381156413 : Nat.Prime 906381156413 := by
  apply lucas_primality 906381156413 (2 : ZMod 906381156413)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (285569, 1), (793487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (285569, 1), (793487, 1)] : List FactorBlock).map factorBlockValue).prod) = 906381156413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_285569
      · exact prime_ninetySevenCQ_793487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 906381156413) ^ 453190578206 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 906381156413) ^ 3173948 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 906381156413) ^ 1142276 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_962726049053 : Nat.Prime 962726049053 := by
  apply lucas_primality 962726049053 (2 : ZMod 962726049053)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9371, 1), (25683653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9371, 1), (25683653, 1)] : List FactorBlock).map factorBlockValue).prod) = 962726049053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_9371
      · exact prime_ninetySevenCQ_25683653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 962726049053) ^ 481363024526 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 962726049053) ^ 102734612 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 962726049053) ^ 37484 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1180346685863 : Nat.Prime 1180346685863 := by
  apply lucas_primality 1180346685863 (5 : ZMod 1180346685863)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (569, 1), (6961151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (569, 1), (6961151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1180346685863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_149
      · exact prime_ninetySevenCQ_569
      · exact prime_ninetySevenCQ_6961151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1180346685863) ^ 590173342931 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1180346685863) ^ 7921789838 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1180346685863) ^ 2074422998 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1180346685863) ^ 169562 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1387303331699 : Nat.Prime 1387303331699 := by
  apply lucas_primality 1387303331699 (2 : ZMod 1387303331699)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (141853, 1), (4889933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (141853, 1), (4889933, 1)] : List FactorBlock).map factorBlockValue).prod) = 1387303331699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_141853
      · exact prime_ninetySevenCQ_4889933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1387303331699) ^ 693651665849 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1387303331699) ^ 9779866 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1387303331699) ^ 283706 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1759003008023 : Nat.Prime 1759003008023 := by
  apply lucas_primality 1759003008023 (5 : ZMod 1759003008023)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (127, 1), (532708361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (127, 1), (532708361, 1)] : List FactorBlock).map factorBlockValue).prod) = 1759003008023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_127
      · exact prime_ninetySevenCQ_532708361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1759003008023) ^ 879501504011 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1759003008023) ^ 135307923694 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1759003008023) ^ 13850417386 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1759003008023) ^ 3302 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2073913890343 : Nat.Prime 2073913890343 := by
  apply lucas_primality 2073913890343 (3 : ZMod 2073913890343)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (103, 1), (691, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (103, 1), (691, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) = 2073913890343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_37
      · exact prime_ninetySevenCQ_103
      · exact prime_ninetySevenCQ_691
      · exact prime_ninetySevenCQ_1103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2073913890343) ^ 1036956945171 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2073913890343) ^ 691304630114 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2073913890343) ^ 296273412906 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2073913890343) ^ 121994934726 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2073913890343) ^ 56051726766 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2073913890343) ^ 20135086314 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2073913890343) ^ 3001322562 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2073913890343) ^ 1880248314 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2255991565649 : Nat.Prime 2255991565649 := by
  apply lucas_primality 2255991565649 (3 : ZMod 2255991565649)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (41, 1), (569, 1), (318103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (41, 1), (569, 1), (318103, 1)] : List FactorBlock).map factorBlockValue).prod) = 2255991565649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_41
      · exact prime_ninetySevenCQ_569
      · exact prime_ninetySevenCQ_318103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2255991565649) ^ 1127995782824 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2255991565649) ^ 118736398192 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2255991565649) ^ 55024184528 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2255991565649) ^ 3964835792 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2255991565649) ^ 7092016 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2373182501803 : Nat.Prime 2373182501803 := by
  apply lucas_primality 2373182501803 (2 : ZMod 2373182501803)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (569, 1), (99304649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (569, 1), (99304649, 1)] : List FactorBlock).map factorBlockValue).prod) = 2373182501803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_569
      · exact prime_ninetySevenCQ_99304649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2373182501803) ^ 1186591250901 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2373182501803) ^ 791060833934 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2373182501803) ^ 339026071686 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2373182501803) ^ 4170795258 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2373182501803) ^ 23898 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2725416914377 : Nat.Prime 2725416914377 := by
  apply lucas_primality 2725416914377 (5 : ZMod 2725416914377)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 2), (103, 1), (6523757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 2), (103, 1), (6523757, 1)] : List FactorBlock).map factorBlockValue).prod) = 2725416914377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_103
      · exact prime_ninetySevenCQ_6523757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2725416914377) ^ 1362708457188 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2725416914377) ^ 908472304792 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2725416914377) ^ 209647454952 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2725416914377) ^ 26460358392 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2725416914377) ^ 417768 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2769416314891 : Nat.Prime 2769416314891 := by
  apply lucas_primality 2769416314891 (2 : ZMod 2769416314891)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (71, 1), (10607, 1), (122579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (71, 1), (10607, 1), (122579, 1)] : List FactorBlock).map factorBlockValue).prod) = 2769416314891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_71
      · exact prime_ninetySevenCQ_10607
      · exact prime_ninetySevenCQ_122579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2769416314891) ^ 1384708157445 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2769416314891) ^ 923138771630 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2769416314891) ^ 553883262978 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2769416314891) ^ 39005863590 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2769416314891) ^ 261093270 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2769416314891) ^ 22592910 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_3603434204647 : Nat.Prime 3603434204647 := by
  apply lucas_primality 3603434204647 (3 : ZMod 3603434204647)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (419, 1), (159260771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (419, 1), (159260771, 1)] : List FactorBlock).map factorBlockValue).prod) = 3603434204647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_419
      · exact prime_ninetySevenCQ_159260771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3603434204647) ^ 1801717102323 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3603434204647) ^ 1201144734882 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3603434204647) ^ 8600081634 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3603434204647) ^ 22626 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_3768671762893 : Nat.Prime 3768671762893 := by
  apply lucas_primality 3768671762893 (2 : ZMod 3768671762893)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (104685326747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (104685326747, 1)] : List FactorBlock).map factorBlockValue).prod) = 3768671762893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_104685326747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3768671762893) ^ 1884335881446 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3768671762893) ^ 1256223920964 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3768671762893) ^ 36 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_5153032513297 : Nat.Prime 5153032513297 := by
  apply lucas_primality 5153032513297 (10 : ZMod 5153032513297)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (37, 1), (322386919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (37, 1), (322386919, 1)] : List FactorBlock).map factorBlockValue).prod) = 5153032513297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_37
      · exact prime_ninetySevenCQ_322386919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 5153032513297) ^ 2576516256648 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 5153032513297) ^ 1717677504432 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 5153032513297) ^ 139271149008 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 5153032513297) ^ 15984 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_5759368700861 : Nat.Prime 5759368700861 := by
  apply lucas_primality 5759368700861 (2 : ZMod 5759368700861)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (211, 1), (59338231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (211, 1), (59338231, 1)] : List FactorBlock).map factorBlockValue).prod) = 5759368700861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_211
      · exact prime_ninetySevenCQ_59338231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5759368700861) ^ 2879684350430 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5759368700861) ^ 1151873740172 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5759368700861) ^ 250407334820 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5759368700861) ^ 27295586260 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5759368700861) ^ 97060 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_9012540078589 : Nat.Prime 9012540078589 := by
  apply lucas_primality 9012540078589 (2 : ZMod 9012540078589)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (109, 1), (160240027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (109, 1), (160240027, 1)] : List FactorBlock).map factorBlockValue).prod) = 9012540078589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_43
      · exact prime_ninetySevenCQ_109
      · exact prime_ninetySevenCQ_160240027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9012540078589) ^ 4506270039294 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9012540078589) ^ 3004180026196 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9012540078589) ^ 209593955316 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9012540078589) ^ 82683853932 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9012540078589) ^ 56244 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_9103054469161 : Nat.Prime 9103054469161 := by
  apply lucas_primality 9103054469161 (17 : ZMod 9103054469161)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (31, 1), (41, 1), (2594971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (31, 1), (41, 1), (2594971, 1)] : List FactorBlock).map factorBlockValue).prod) = 9103054469161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_41
      · exact prime_ninetySevenCQ_2594971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 9103054469161) ^ 4551527234580 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (17 : ZMod 9103054469161) ^ 3034351489720 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (17 : ZMod 9103054469161) ^ 1820610893832 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (17 : ZMod 9103054469161) ^ 395784976920 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (17 : ZMod 9103054469161) ^ 293646918360 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (17 : ZMod 9103054469161) ^ 222025718760 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (17 : ZMod 9103054469161) ^ 3507960 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_12902403650321 : Nat.Prime 12902403650321 := by
  apply lucas_primality 12902403650321 (3 : ZMod 12902403650321)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1103, 1), (146219443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1103, 1), (146219443, 1)] : List FactorBlock).map factorBlockValue).prod) = 12902403650321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_1103
      · exact prime_ninetySevenCQ_146219443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12902403650321) ^ 6451201825160 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12902403650321) ^ 2580480730064 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12902403650321) ^ 11697555440 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12902403650321) ^ 88240 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_15102042076129 : Nat.Prime 15102042076129 := by
  apply lucas_primality 15102042076129 (11 : ZMod 15102042076129)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (97, 1), (231683267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (97, 1), (231683267, 1)] : List FactorBlock).map factorBlockValue).prod) = 15102042076129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_97
      · exact prime_ninetySevenCQ_231683267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 15102042076129) ^ 7551021038064 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 15102042076129) ^ 5034014025376 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 15102042076129) ^ 2157434582304 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 15102042076129) ^ 155691155424 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 15102042076129) ^ 65184 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_16700914664563 : Nat.Prime 16700914664563 := by
  apply lucas_primality 16700914664563 (3 : ZMod 16700914664563)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (787, 1), (8699, 1), (406579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (787, 1), (8699, 1), (406579, 1)] : List FactorBlock).map factorBlockValue).prod) = 16700914664563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_787
      · exact prime_ninetySevenCQ_8699
      · exact prime_ninetySevenCQ_406579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16700914664563) ^ 8350457332281 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 16700914664563) ^ 5566971554854 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 16700914664563) ^ 21220984326 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 16700914664563) ^ 1919866038 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 16700914664563) ^ 41076678 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_18918108683059 : Nat.Prime 18918108683059 := by
  apply lucas_primality 18918108683059 (2 : ZMod 18918108683059)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (419, 1), (578854069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (419, 1), (578854069, 1)] : List FactorBlock).map factorBlockValue).prod) = 18918108683059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_419
      · exact prime_ninetySevenCQ_578854069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18918108683059) ^ 9459054341529 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 18918108683059) ^ 6306036227686 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 18918108683059) ^ 1455239129466 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 18918108683059) ^ 45150617382 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 18918108683059) ^ 32682 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_24207519390017 : Nat.Prime 24207519390017 := by
  apply lucas_primality 24207519390017 (3 : ZMod 24207519390017)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (821, 1), (2803, 1), (164363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (821, 1), (2803, 1), (164363, 1)] : List FactorBlock).map factorBlockValue).prod) = 24207519390017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_821
      · exact prime_ninetySevenCQ_2803
      · exact prime_ninetySevenCQ_164363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 24207519390017) ^ 12103759695008 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 24207519390017) ^ 29485407296 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 24207519390017) ^ 8636289472 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 24207519390017) ^ 147280832 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_24424842666109 : Nat.Prime 24424842666109 := by
  apply lucas_primality 24424842666109 (2 : ZMod 24424842666109)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (397, 1), (5126961097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (397, 1), (5126961097, 1)] : List FactorBlock).map factorBlockValue).prod) = 24424842666109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_397
      · exact prime_ninetySevenCQ_5126961097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24424842666109) ^ 12212421333054 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 24424842666109) ^ 8141614222036 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 24424842666109) ^ 61523533164 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 24424842666109) ^ 4764 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_27943006912771 : Nat.Prime 27943006912771 := by
  apply lucas_primality 27943006912771 (2 : ZMod 27943006912771)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (2003, 1), (2767, 1), (4099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (2003, 1), (2767, 1), (4099, 1)] : List FactorBlock).map factorBlockValue).prod) = 27943006912771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_41
      · exact prime_ninetySevenCQ_2003
      · exact prime_ninetySevenCQ_2767
      · exact prime_ninetySevenCQ_4099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27943006912771) ^ 13971503456385 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 27943006912771) ^ 9314335637590 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 27943006912771) ^ 5588601382554 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 27943006912771) ^ 681536753970 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 27943006912771) ^ 13950577590 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 27943006912771) ^ 10098665310 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 27943006912771) ^ 6817030230 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_29006399301883 : Nat.Prime 29006399301883 := by
  apply lucas_primality 29006399301883 (2 : ZMod 29006399301883)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 2), (149, 1), (743, 1), (82549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 2), (149, 1), (743, 1), (82549, 1)] : List FactorBlock).map factorBlockValue).prod) = 29006399301883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_149
      · exact prime_ninetySevenCQ_743
      · exact prime_ninetySevenCQ_82549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29006399301883) ^ 14503199650941 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 29006399301883) ^ 9668799767294 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 29006399301883) ^ 1261147795734 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 29006399301883) ^ 194673820818 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 29006399301883) ^ 39039568374 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 29006399301883) ^ 351384018 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_30268425737483 : Nat.Prime 30268425737483 := by
  apply lucas_primality 30268425737483 (2 : ZMod 30268425737483)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (929, 1), (16290864229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (929, 1), (16290864229, 1)] : List FactorBlock).map factorBlockValue).prod) = 30268425737483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_929
      · exact prime_ninetySevenCQ_16290864229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30268425737483) ^ 15134212868741 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 30268425737483) ^ 32581728458 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 30268425737483) ^ 1858 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_31265150842831 : Nat.Prime 31265150842831 := by
  apply lucas_primality 31265150842831 (6 : ZMod 31265150842831)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (269419, 1), (3868219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (269419, 1), (3868219, 1)] : List FactorBlock).map factorBlockValue).prod) = 31265150842831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_269419
      · exact prime_ninetySevenCQ_3868219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 31265150842831) ^ 15632575421415 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 31265150842831) ^ 10421716947610 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 31265150842831) ^ 6253030168566 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 31265150842831) ^ 116046570 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 31265150842831) ^ 8082570 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_34387724799283 : Nat.Prime 34387724799283 := by
  apply lucas_primality 34387724799283 (3 : ZMod 34387724799283)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (593, 1), (420213173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (593, 1), (420213173, 1)] : List FactorBlock).map factorBlockValue).prod) = 34387724799283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_593
      · exact prime_ninetySevenCQ_420213173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34387724799283) ^ 17193862399641 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 34387724799283) ^ 11462574933094 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 34387724799283) ^ 1495118469534 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 34387724799283) ^ 57989417874 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 34387724799283) ^ 81834 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_38897677166321 : Nat.Prime 38897677166321 := by
  apply lucas_primality 38897677166321 (3 : ZMod 38897677166321)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (69460137797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (69460137797, 1)] : List FactorBlock).map factorBlockValue).prod) = 38897677166321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_69460137797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38897677166321) ^ 19448838583160 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38897677166321) ^ 7779535433264 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38897677166321) ^ 5556811023760 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38897677166321) ^ 560 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_49235883827597 : Nat.Prime 49235883827597 := by
  apply lucas_primality 49235883827597 (2 : ZMod 49235883827597)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (461, 1), (721637507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (461, 1), (721637507, 1)] : List FactorBlock).map factorBlockValue).prod) = 49235883827597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_37
      · exact prime_ninetySevenCQ_461
      · exact prime_ninetySevenCQ_721637507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49235883827597) ^ 24617941913798 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 49235883827597) ^ 1330699562908 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 49235883827597) ^ 106802351036 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 49235883827597) ^ 68228 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_82385298665231 : Nat.Prime 82385298665231 := by
  apply lucas_primality 82385298665231 (7 : ZMod 82385298665231)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (3593, 1), (9007, 1), (23143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (3593, 1), (9007, 1), (23143, 1)] : List FactorBlock).map factorBlockValue).prod) = 82385298665231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_3593
      · exact prime_ninetySevenCQ_9007
      · exact prime_ninetySevenCQ_23143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 82385298665231) ^ 41192649332615 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 82385298665231) ^ 16477059733046 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 82385298665231) ^ 7489572605930 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 82385298665231) ^ 22929390110 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 82385298665231) ^ 9146807890 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 82385298665231) ^ 3559836610 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_88573981465117 : Nat.Prime 88573981465117 := by
  apply lucas_primality 88573981465117 (5 : ZMod 88573981465117)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (19, 1), (101, 1), (183160007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (19, 1), (101, 1), (183160007, 1)] : List FactorBlock).map factorBlockValue).prod) = 88573981465117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_101
      · exact prime_ninetySevenCQ_183160007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 88573981465117) ^ 44286990732558 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 88573981465117) ^ 29524660488372 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 88573981465117) ^ 12653425923588 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 88573981465117) ^ 4661788498164 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 88573981465117) ^ 876970113516 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 88573981465117) ^ 483588 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_89985171131707 : Nat.Prime 89985171131707 := by
  apply lucas_primality 89985171131707 (2 : ZMod 89985171131707)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3312107, 1), (4528093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3312107, 1), (4528093, 1)] : List FactorBlock).map factorBlockValue).prod) = 89985171131707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_3312107
      · exact prime_ninetySevenCQ_4528093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 89985171131707) ^ 44992585565853 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 89985171131707) ^ 29995057043902 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 89985171131707) ^ 27168558 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 89985171131707) ^ 19872642 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_94146660164153 : Nat.Prime 94146660164153 := by
  apply lucas_primality 94146660164153 (3 : ZMod 94146660164153)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67699, 1), (173833181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67699, 1), (173833181, 1)] : List FactorBlock).map factorBlockValue).prod) = 94146660164153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_67699
      · exact prime_ninetySevenCQ_173833181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 94146660164153) ^ 47073330082076 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 94146660164153) ^ 1390665448 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 94146660164153) ^ 541592 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_109166395082939 : Nat.Prime 109166395082939 := by
  apply lucas_primality 109166395082939 (2 : ZMod 109166395082939)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (2373182501803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (2373182501803, 1)] : List FactorBlock).map factorBlockValue).prod) = 109166395082939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_2373182501803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 109166395082939) ^ 54583197541469 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 109166395082939) ^ 4746365003606 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 109166395082939) ^ 46 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_144129233618323 : Nat.Prime 144129233618323 := by
  apply lucas_primality 144129233618323 (2 : ZMod 144129233618323)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (138461, 1), (173489567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (138461, 1), (173489567, 1)] : List FactorBlock).map factorBlockValue).prod) = 144129233618323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_138461
      · exact prime_ninetySevenCQ_173489567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 144129233618323) ^ 72064616809161 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 144129233618323) ^ 48043077872774 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 144129233618323) ^ 1040937402 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 144129233618323) ^ 830766 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_163791396802463 : Nat.Prime 163791396802463 := by
  apply lucas_primality 163791396802463 (10 : ZMod 163791396802463)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (53, 1), (18773, 1), (575593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (53, 1), (18773, 1), (575593, 1)] : List FactorBlock).map factorBlockValue).prod) = 163791396802463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_53
      · exact prime_ninetySevenCQ_18773
      · exact prime_ninetySevenCQ_575593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 163791396802463) ^ 81895698401231 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 163791396802463) ^ 14890126982042 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 163791396802463) ^ 12599338215574 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 163791396802463) ^ 3090403713254 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 163791396802463) ^ 8724838694 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 163791396802463) ^ 284561134 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_165303149698733 : Nat.Prime 165303149698733 := by
  apply lucas_primality 165303149698733 (2 : ZMod 165303149698733)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3919, 1), (4679, 1), (2253683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3919, 1), (4679, 1), (2253683, 1)] : List FactorBlock).map factorBlockValue).prod) = 165303149698733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3919
      · exact prime_ninetySevenCQ_4679
      · exact prime_ninetySevenCQ_2253683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 165303149698733) ^ 82651574849366 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 165303149698733) ^ 42179931028 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 165303149698733) ^ 35328734708 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 165303149698733) ^ 73348004 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_228497352719047 : Nat.Prime 228497352719047 := by
  apply lucas_primality 228497352719047 (3 : ZMod 228497352719047)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (3313, 1), (171566971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (3313, 1), (171566971, 1)] : List FactorBlock).map factorBlockValue).prod) = 228497352719047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_67
      · exact prime_ninetySevenCQ_3313
      · exact prime_ninetySevenCQ_171566971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 228497352719047) ^ 114248676359523 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 228497352719047) ^ 76165784239682 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 228497352719047) ^ 3410408249538 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 228497352719047) ^ 68969922342 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 228497352719047) ^ 1331826 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_271836757370323 : Nat.Prime 271836757370323 := by
  apply lucas_primality 271836757370323 (2 : ZMod 271836757370323)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (15102042076129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (15102042076129, 1)] : List FactorBlock).map factorBlockValue).prod) = 271836757370323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_15102042076129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 271836757370323) ^ 135918378685161 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 271836757370323) ^ 90612252456774 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 271836757370323) ^ 18 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_281899222298891 : Nat.Prime 281899222298891 := by
  apply lucas_primality 281899222298891 (2 : ZMod 281899222298891)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (37, 1), (1789, 1), (60839239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (37, 1), (1789, 1), (60839239, 1)] : List FactorBlock).map factorBlockValue).prod) = 281899222298891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_37
      · exact prime_ninetySevenCQ_1789
      · exact prime_ninetySevenCQ_60839239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 281899222298891) ^ 140949611149445 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 281899222298891) ^ 56379844459778 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 281899222298891) ^ 40271317471270 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 281899222298891) ^ 7618897899970 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 281899222298891) ^ 157573629010 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 281899222298891) ^ 4633510 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_317372828660401 : Nat.Prime 317372828660401 := by
  apply lucas_primality 317372828660401 (7 : ZMod 317372828660401)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (17, 1), (15557491601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (17, 1), (15557491601, 1)] : List FactorBlock).map factorBlockValue).prod) = 317372828660401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_15557491601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 317372828660401) ^ 158686414330200 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 317372828660401) ^ 105790942886800 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 317372828660401) ^ 63474565732080 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 317372828660401) ^ 18668989921200 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 317372828660401) ^ 20400 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_470428972822013 : Nat.Prime 470428972822013 := by
  apply lucas_primality 470428972822013 (2 : ZMod 470428972822013)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (593, 1), (198325873871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (593, 1), (198325873871, 1)] : List FactorBlock).map factorBlockValue).prod) = 470428972822013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_593
      · exact prime_ninetySevenCQ_198325873871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 470428972822013) ^ 235214486411006 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 470428972822013) ^ 793303495484 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 470428972822013) ^ 2372 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_523845546942023 : Nat.Prime 523845546942023 := by
  apply lucas_primality 523845546942023 (5 : ZMod 523845546942023)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (67, 1), (3347, 1), (68705867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (67, 1), (3347, 1), (68705867, 1)] : List FactorBlock).map factorBlockValue).prod) = 523845546942023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_67
      · exact prime_ninetySevenCQ_3347
      · exact prime_ninetySevenCQ_68705867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 523845546942023) ^ 261922773471011 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 523845546942023) ^ 30814443937766 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 523845546942023) ^ 7818590252866 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 523845546942023) ^ 156511965026 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 523845546942023) ^ 7624466 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_567831098595143 : Nat.Prime 567831098595143 := by
  apply lucas_primality 567831098595143 (5 : ZMod 567831098595143)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (16700914664563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (16700914664563, 1)] : List FactorBlock).map factorBlockValue).prod) = 567831098595143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_16700914664563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 567831098595143) ^ 283915549297571 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 567831098595143) ^ 33401829329126 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 567831098595143) ^ 34 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_634600215751519 : Nat.Prime 634600215751519 := by
  apply lucas_primality 634600215751519 (15 : ZMod 634600215751519)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (157, 1), (2705515121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (157, 1), (2705515121, 1)] : List FactorBlock).map factorBlockValue).prod) = 634600215751519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_83
      · exact prime_ninetySevenCQ_157
      · exact prime_ninetySevenCQ_2705515121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 634600215751519) ^ 317300107875759 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (15 : ZMod 634600215751519) ^ 211533405250506 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (15 : ZMod 634600215751519) ^ 7645785731946 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (15 : ZMod 634600215751519) ^ 4042039590774 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (15 : ZMod 634600215751519) ^ 234558 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_690583148342071 : Nat.Prime 690583148342071 := by
  apply lucas_primality 690583148342071 (3 : ZMod 690583148342071)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (9337, 1), (79529027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (9337, 1), (79529027, 1)] : List FactorBlock).map factorBlockValue).prod) = 690583148342071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_9337
      · exact prime_ninetySevenCQ_79529027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 690583148342071) ^ 345291574171035 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 690583148342071) ^ 230194382780690 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 690583148342071) ^ 138116629668414 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 690583148342071) ^ 22276875752970 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 690583148342071) ^ 73961995110 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 690583148342071) ^ 8683410 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_720400676940937 : Nat.Prime 720400676940937 := by
  apply lucas_primality 720400676940937 (5 : ZMod 720400676940937)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (331, 1), (13597, 1), (741053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (331, 1), (13597, 1), (741053, 1)] : List FactorBlock).map factorBlockValue).prod) = 720400676940937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_331
      · exact prime_ninetySevenCQ_13597
      · exact prime_ninetySevenCQ_741053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 720400676940937) ^ 360200338470468 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 720400676940937) ^ 240133558980312 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 720400676940937) ^ 2176437090456 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 720400676940937) ^ 52982325288 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 720400676940937) ^ 972131112 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_885739814651171 : Nat.Prime 885739814651171 := by
  apply lucas_primality 885739814651171 (2 : ZMod 885739814651171)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (88573981465117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (88573981465117, 1)] : List FactorBlock).map factorBlockValue).prod) = 885739814651171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_88573981465117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 885739814651171) ^ 442869907325585 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 885739814651171) ^ 177147962930234 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 885739814651171) ^ 10 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_890722488704537 : Nat.Prime 890722488704537 := by
  apply lucas_primality 890722488704537 (3 : ZMod 890722488704537)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1289, 1), (107101, 1), (806503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1289, 1), (107101, 1), (806503, 1)] : List FactorBlock).map factorBlockValue).prod) = 890722488704537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_1289
      · exact prime_ninetySevenCQ_107101
      · exact prime_ninetySevenCQ_806503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 890722488704537) ^ 445361244352268 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 890722488704537) ^ 691018222424 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 890722488704537) ^ 8316658936 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 890722488704537) ^ 1104425512 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1439762738107313 : Nat.Prime 1439762738107313 := by
  apply lucas_primality 1439762738107313 (3 : ZMod 1439762738107313)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (89985171131707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (89985171131707, 1)] : List FactorBlock).map factorBlockValue).prod) = 1439762738107313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_89985171131707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1439762738107313) ^ 719881369053656 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1439762738107313) ^ 16 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1553386151736737 : Nat.Prime 1553386151736737 := by
  apply lucas_primality 1553386151736737 (3 : ZMod 1553386151736737)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (47, 1), (313, 1), (3299797243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (47, 1), (313, 1), (3299797243, 1)] : List FactorBlock).map factorBlockValue).prod) = 1553386151736737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_47
      · exact prime_ninetySevenCQ_313
      · exact prime_ninetySevenCQ_3299797243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1553386151736737) ^ 776693075868368 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1553386151736737) ^ 33050769185888 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1553386151736737) ^ 4962895053472 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1553386151736737) ^ 470752 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1594372113927443 : Nat.Prime 1594372113927443 := by
  apply lucas_primality 1594372113927443 (2 : ZMod 1594372113927443)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (461, 1), (23671, 1), (73053691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (461, 1), (23671, 1), (73053691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1594372113927443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_461
      · exact prime_ninetySevenCQ_23671
      · exact prime_ninetySevenCQ_73053691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1594372113927443) ^ 797186056963721 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1594372113927443) ^ 3458507839322 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1594372113927443) ^ 67355503102 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1594372113927443) ^ 21824662 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2778475035927649 : Nat.Prime 2778475035927649 := by
  apply lucas_primality 2778475035927649 (13 : ZMod 2778475035927649)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (31, 1), (137, 1), (400870487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (31, 1), (137, 1), (400870487, 1)] : List FactorBlock).map factorBlockValue).prod) = 2778475035927649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_137
      · exact prime_ninetySevenCQ_400870487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2778475035927649) ^ 1389237517963824 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2778475035927649) ^ 926158345309216 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2778475035927649) ^ 163439707995744 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2778475035927649) ^ 89628226965408 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2778475035927649) ^ 20280839678304 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2778475035927649) ^ 6931104 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_4068480283297979 : Nat.Prime 4068480283297979 := by
  apply lucas_primality 4068480283297979 (2 : ZMod 4068480283297979)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2113, 1), (962726049053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2113, 1), (962726049053, 1)] : List FactorBlock).map factorBlockValue).prod) = 4068480283297979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_2113
      · exact prime_ninetySevenCQ_962726049053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4068480283297979) ^ 2034240141648989 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4068480283297979) ^ 1925452098106 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4068480283297979) ^ 4226 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_4487650379014801 : Nat.Prime 4487650379014801 := by
  apply lucas_primality 4487650379014801 (7 : ZMod 4487650379014801)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (83, 1), (45056730713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (83, 1), (45056730713, 1)] : List FactorBlock).map factorBlockValue).prod) = 4487650379014801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_83
      · exact prime_ninetySevenCQ_45056730713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4487650379014801) ^ 2243825189507400 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4487650379014801) ^ 1495883459671600 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4487650379014801) ^ 897530075802960 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4487650379014801) ^ 54068076855600 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 4487650379014801) ^ 99600 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_5409678109598233 : Nat.Prime 5409678109598233 := by
  apply lucas_primality 5409678109598233 (5 : ZMod 5409678109598233)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (113, 1), (3797, 1), (525340813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (113, 1), (3797, 1), (525340813, 1)] : List FactorBlock).map factorBlockValue).prod) = 5409678109598233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_113
      · exact prime_ninetySevenCQ_3797
      · exact prime_ninetySevenCQ_525340813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5409678109598233) ^ 2704839054799116 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 5409678109598233) ^ 1803226036532744 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 5409678109598233) ^ 47873257607064 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 5409678109598233) ^ 1424724284856 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 5409678109598233) ^ 10297464 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_5720259861641323 : Nat.Prime 5720259861641323 := by
  apply lucas_primality 5720259861641323 (3 : ZMod 5720259861641323)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 2), (293436947863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 2), (293436947863, 1)] : List FactorBlock).map factorBlockValue).prod) = 5720259861641323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_293436947863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5720259861641323) ^ 2860129930820661 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5720259861641323) ^ 1906753287213774 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5720259861641323) ^ 301066308507438 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5720259861641323) ^ 19494 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_7267639144310011 : Nat.Prime 7267639144310011 := by
  apply lucas_primality 7267639144310011 (2 : ZMod 7267639144310011)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (347, 1), (25857043243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (347, 1), (25857043243, 1)] : List FactorBlock).map factorBlockValue).prod) = 7267639144310011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_347
      · exact prime_ninetySevenCQ_25857043243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7267639144310011) ^ 3633819572155005 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7267639144310011) ^ 2422546381436670 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7267639144310011) ^ 1453527828862002 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7267639144310011) ^ 20944205026830 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7267639144310011) ^ 281070 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_7486076943793559 : Nat.Prime 7486076943793559 := by
  apply lucas_primality 7486076943793559 (11 : ZMod 7486076943793559)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (1451, 1), (13794795667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (1451, 1), (13794795667, 1)] : List FactorBlock).map factorBlockValue).prod) = 7486076943793559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_1451
      · exact prime_ninetySevenCQ_13794795667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7486076943793559) ^ 3743038471896779 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7486076943793559) ^ 680552449435778 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7486076943793559) ^ 440357467281974 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7486076943793559) ^ 5159253579458 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7486076943793559) ^ 542674 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_15759032337051121 : Nat.Prime 15759032337051121 := by
  apply lucas_primality 15759032337051121 (7 : ZMod 15759032337051121)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (13, 1), (101, 1), (139, 1), (3463, 1), (34631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (13, 1), (101, 1), (139, 1), (3463, 1), (34631, 1)] : List FactorBlock).map factorBlockValue).prod) = 15759032337051121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_101
      · exact prime_ninetySevenCQ_139
      · exact prime_ninetySevenCQ_3463
      · exact prime_ninetySevenCQ_34631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15759032337051121) ^ 7879516168525560 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15759032337051121) ^ 5253010779017040 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15759032337051121) ^ 3151806467410224 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15759032337051121) ^ 1212233256696240 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15759032337051121) ^ 156030023139120 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15759032337051121) ^ 113374333360080 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15759032337051121) ^ 4550687940240 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15759032337051121) ^ 455055653520 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_16842395227140851 : Nat.Prime 16842395227140851 := by
  apply lucas_primality 16842395227140851 (7 : ZMod 16842395227140851)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23, 1), (47977, 1), (305262127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23, 1), (47977, 1), (305262127, 1)] : List FactorBlock).map factorBlockValue).prod) = 16842395227140851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_47977
      · exact prime_ninetySevenCQ_305262127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16842395227140851) ^ 8421197613570425 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16842395227140851) ^ 3368479045428170 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16842395227140851) ^ 732278053353950 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16842395227140851) ^ 351051446050 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 16842395227140851) ^ 55173550 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_19823568537041327 : Nat.Prime 19823568537041327 := by
  apply lucas_primality 19823568537041327 (5 : ZMod 19823568537041327)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (55117, 1), (6201093391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (55117, 1), (6201093391, 1)] : List FactorBlock).map factorBlockValue).prod) = 19823568537041327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_29
      · exact prime_ninetySevenCQ_55117
      · exact prime_ninetySevenCQ_6201093391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19823568537041327) ^ 9911784268520663 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 19823568537041327) ^ 683571328863494 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 19823568537041327) ^ 359663416678 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 19823568537041327) ^ 3196786 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_23030038459851629 : Nat.Prime 23030038459851629 := by
  apply lucas_primality 23030038459851629 (2 : ZMod 23030038459851629)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (673, 1), (41443, 1), (10864627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (673, 1), (41443, 1), (10864627, 1)] : List FactorBlock).map factorBlockValue).prod) = 23030038459851629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_673
      · exact prime_ninetySevenCQ_41443
      · exact prime_ninetySevenCQ_10864627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23030038459851629) ^ 11515019229925814 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 23030038459851629) ^ 1212107287360612 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 23030038459851629) ^ 34219967993836 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 23030038459851629) ^ 555703941796 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 23030038459851629) ^ 2119726564 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_23321389939581809 : Nat.Prime 23321389939581809 := by
  apply lucas_primality 23321389939581809 (3 : ZMod 23321389939581809)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (41, 1), (151, 1), (1543, 1), (8975503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (41, 1), (151, 1), (1543, 1), (8975503, 1)] : List FactorBlock).map factorBlockValue).prod) = 23321389939581809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_41
      · exact prime_ninetySevenCQ_151
      · exact prime_ninetySevenCQ_1543
      · exact prime_ninetySevenCQ_8975503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23321389939581809) ^ 11660694969790904 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23321389939581809) ^ 1371846467034224 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23321389939581809) ^ 568814388770288 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23321389939581809) ^ 154446290990608 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23321389939581809) ^ 15114316227856 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23321389939581809) ^ 2598337936 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_42280009219535959 : Nat.Prime 42280009219535959 := by
  apply lucas_primality 42280009219535959 (11 : ZMod 42280009219535959)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (71, 1), (5039, 1), (17401, 1), (29023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (71, 1), (5039, 1), (17401, 1), (29023, 1)] : List FactorBlock).map factorBlockValue).prod) = 42280009219535959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_71
      · exact prime_ninetySevenCQ_5039
      · exact prime_ninetySevenCQ_17401
      · exact prime_ninetySevenCQ_29023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 42280009219535959) ^ 21140004609767979 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 42280009219535959) ^ 14093336406511986 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 42280009219535959) ^ 3252308401502766 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 42280009219535959) ^ 595493087599098 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 42280009219535959) ^ 8390555510922 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 42280009219535959) ^ 2429745946758 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 42280009219535959) ^ 1456775978346 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_44878058532963731 : Nat.Prime 44878058532963731 := by
  apply lucas_primality 44878058532963731 (2 : ZMod 44878058532963731)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (29, 1), (9103054469161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (29, 1), (9103054469161, 1)] : List FactorBlock).map factorBlockValue).prod) = 44878058532963731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_29
      · exact prime_ninetySevenCQ_9103054469161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44878058532963731) ^ 22439029266481865 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 44878058532963731) ^ 8975611706592746 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 44878058532963731) ^ 2639885796056690 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 44878058532963731) ^ 1547519259757370 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 44878058532963731) ^ 4930 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_46642779879163619 : Nat.Prime 46642779879163619 := by
  apply lucas_primality 46642779879163619 (2 : ZMod 46642779879163619)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23321389939581809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23321389939581809, 1)] : List FactorBlock).map factorBlockValue).prod) = 46642779879163619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_23321389939581809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 46642779879163619) ^ 23321389939581809 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 46642779879163619) ^ 2 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_49163860943746877 : Nat.Prime 49163860943746877 := by
  apply lucas_primality 49163860943746877 (2 : ZMod 49163860943746877)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (107, 1), (157, 1), (9421, 1), (77661461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (107, 1), (157, 1), (9421, 1), (77661461, 1)] : List FactorBlock).map factorBlockValue).prod) = 49163860943746877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_107
      · exact prime_ninetySevenCQ_157
      · exact prime_ninetySevenCQ_9421
      · exact prime_ninetySevenCQ_77661461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49163860943746877) ^ 24581930471873438 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 49163860943746877) ^ 459475335922868 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 49163860943746877) ^ 313145611106668 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 49163860943746877) ^ 5218539533356 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 49163860943746877) ^ 633053516 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_53144388879070261 : Nat.Prime 53144388879070261 := by
  apply lucas_primality 53144388879070261 (6 : ZMod 53144388879070261)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (885739814651171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (885739814651171, 1)] : List FactorBlock).map factorBlockValue).prod) = 53144388879070261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_885739814651171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 53144388879070261) ^ 26572194439535130 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 53144388879070261) ^ 17714796293023420 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 53144388879070261) ^ 10628877775814052 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 53144388879070261) ^ 60 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_60815510215005613 : Nat.Prime 60815510215005613 := by
  apply lucas_primality 60815510215005613 (2 : ZMod 60815510215005613)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (5011, 1), (91942439081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (5011, 1), (91942439081, 1)] : List FactorBlock).map factorBlockValue).prod) = 60815510215005613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_5011
      · exact prime_ninetySevenCQ_91942439081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 60815510215005613) ^ 30407755107502806 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 60815510215005613) ^ 20271836738335204 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 60815510215005613) ^ 5528682746818692 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 60815510215005613) ^ 12136401958692 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 60815510215005613) ^ 661452 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_81000629293497527 : Nat.Prime 81000629293497527 := by
  apply lucas_primality 81000629293497527 (5 : ZMod 81000629293497527)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (281, 1), (144129233618323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (281, 1), (144129233618323, 1)] : List FactorBlock).map factorBlockValue).prod) = 81000629293497527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_281
      · exact prime_ninetySevenCQ_144129233618323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 81000629293497527) ^ 40500314646748763 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 81000629293497527) ^ 288258467236646 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 81000629293497527) ^ 562 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_97589848846413811 : Nat.Prime 97589848846413811 := by
  apply lucas_primality 97589848846413811 (2 : ZMod 97589848846413811)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (3499, 1), (13876011319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (3499, 1), (13876011319, 1)] : List FactorBlock).map factorBlockValue).prod) = 97589848846413811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_67
      · exact prime_ninetySevenCQ_3499
      · exact prime_ninetySevenCQ_13876011319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 97589848846413811) ^ 48794924423206905 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97589848846413811) ^ 32529949615471270 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97589848846413811) ^ 19517969769282762 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97589848846413811) ^ 1456564908155430 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97589848846413811) ^ 27890782751190 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97589848846413811) ^ 7032990 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_101724933249331709 : Nat.Prime 101724933249331709 := by
  apply lucas_primality 101724933249331709 (2 : ZMod 101724933249331709)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1597, 1), (9479, 1), (1679964029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1597, 1), (9479, 1), (1679964029, 1)] : List FactorBlock).map factorBlockValue).prod) = 101724933249331709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_1597
      · exact prime_ninetySevenCQ_9479
      · exact prime_ninetySevenCQ_1679964029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 101724933249331709) ^ 50862466624665854 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 101724933249331709) ^ 63697516123564 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 101724933249331709) ^ 10731610217252 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 101724933249331709) ^ 60551852 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_255914952088786313 : Nat.Prime 255914952088786313 := by
  apply lucas_primality 255914952088786313 (3 : ZMod 255914952088786313)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (5197, 1), (19031, 1), (46205461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (5197, 1), (19031, 1), (46205461, 1)] : List FactorBlock).map factorBlockValue).prod) = 255914952088786313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_5197
      · exact prime_ninetySevenCQ_19031
      · exact prime_ninetySevenCQ_46205461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 255914952088786313) ^ 127957476044393156 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 255914952088786313) ^ 36559278869826616 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 255914952088786313) ^ 49242823184296 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 255914952088786313) ^ 13447267725752 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 255914952088786313) ^ 5538629992 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_276849518456303041 : Nat.Prime 276849518456303041 := by
  apply lucas_primality 276849518456303041 (13 : ZMod 276849518456303041)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (37, 1), (47, 1), (257, 1), (645267563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (37, 1), (47, 1), (257, 1), (645267563, 1)] : List FactorBlock).map factorBlockValue).prod) = 276849518456303041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_37
      · exact prime_ninetySevenCQ_47
      · exact prime_ninetySevenCQ_257
      · exact prime_ninetySevenCQ_645267563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 276849518456303041) ^ 138424759228151520 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 276849518456303041) ^ 92283172818767680 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 276849518456303041) ^ 55369903691260608 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 276849518456303041) ^ 7482419417737920 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 276849518456303041) ^ 5890415286304320 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 276849518456303041) ^ 1077235480374720 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 276849518456303041) ^ 429046080 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_285386164317263897 : Nat.Prime 285386164317263897 := by
  apply lucas_primality 285386164317263897 (3 : ZMod 285386164317263897)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (5011, 1), (418764254401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (5011, 1), (418764254401, 1)] : List FactorBlock).map factorBlockValue).prod) = 285386164317263897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_5011
      · exact prime_ninetySevenCQ_418764254401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 285386164317263897) ^ 142693082158631948 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 285386164317263897) ^ 16787421430427288 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 285386164317263897) ^ 56951938598536 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 285386164317263897) ^ 681496 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_312141459389180207 : Nat.Prime 312141459389180207 := by
  apply lucas_primality 312141459389180207 (5 : ZMod 312141459389180207)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10631, 1), (593429, 1), (24738797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10631, 1), (593429, 1), (24738797, 1)] : List FactorBlock).map factorBlockValue).prod) = 312141459389180207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_10631
      · exact prime_ninetySevenCQ_593429
      · exact prime_ninetySevenCQ_24738797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 312141459389180207) ^ 156070729694590103 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 312141459389180207) ^ 29361439129826 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 312141459389180207) ^ 525996301814 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 312141459389180207) ^ 12617487398 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_366285037865617027 : Nat.Prime 366285037865617027 := by
  apply lucas_primality 366285037865617027 (3 : ZMod 366285037865617027)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (19, 1), (82385298665231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (19, 1), (82385298665231, 1)] : List FactorBlock).map factorBlockValue).prod) = 366285037865617027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_82385298665231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 366285037865617027) ^ 183142518932808513 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 366285037865617027) ^ 122095012621872342 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 366285037865617027) ^ 28175772143509002 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 366285037865617027) ^ 19278159887664054 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 366285037865617027) ^ 4446 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_420885256131377827 : Nat.Prime 420885256131377827 := by
  apply lucas_primality 420885256131377827 (2 : ZMod 420885256131377827)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193939, 1), (361699001689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193939, 1), (361699001689, 1)] : List FactorBlock).map factorBlockValue).prod) = 420885256131377827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_193939
      · exact prime_ninetySevenCQ_361699001689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 420885256131377827) ^ 210442628065688913 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 420885256131377827) ^ 140295085377125942 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 420885256131377827) ^ 2170194010134 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 420885256131377827) ^ 1163634 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_516218997383341453 : Nat.Prime 516218997383341453 := by
  apply lucas_primality 516218997383341453 (5 : ZMod 516218997383341453)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (23, 1), (29, 1), (113, 1), (10013216443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (23, 1), (29, 1), (113, 1), (10013216443, 1)] : List FactorBlock).map factorBlockValue).prod) = 516218997383341453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_29
      · exact prime_ninetySevenCQ_113
      · exact prime_ninetySevenCQ_10013216443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 516218997383341453) ^ 258109498691670726 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 516218997383341453) ^ 172072999127780484 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 516218997383341453) ^ 27169420914912708 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 516218997383341453) ^ 22444304234058324 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 516218997383341453) ^ 17800655082184188 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 516218997383341453) ^ 4568309711357004 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 516218997383341453) ^ 51553764 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_592369850029953733 : Nat.Prime 592369850029953733 := by
  apply lucas_primality 592369850029953733 (5 : ZMod 592369850029953733)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (4487650379014801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (4487650379014801, 1)] : List FactorBlock).map factorBlockValue).prod) = 592369850029953733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_4487650379014801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 592369850029953733) ^ 296184925014976866 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 592369850029953733) ^ 197456616676651244 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 592369850029953733) ^ 53851804548177612 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 592369850029953733) ^ 132 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_813799465994653673 : Nat.Prime 813799465994653673 := by
  apply lucas_primality 813799465994653673 (3 : ZMod 813799465994653673)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (101724933249331709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (101724933249331709, 1)] : List FactorBlock).map factorBlockValue).prod) = 813799465994653673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_101724933249331709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 813799465994653673) ^ 406899732997326836 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 813799465994653673) ^ 8 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_925107929942445773 : Nat.Prime 925107929942445773 := by
  apply lucas_primality 925107929942445773 (2 : ZMod 925107929942445773)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (127, 1), (91183, 1), (19971689923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (127, 1), (91183, 1), (19971689923, 1)] : List FactorBlock).map factorBlockValue).prod) = 925107929942445773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_127
      · exact prime_ninetySevenCQ_91183
      · exact prime_ninetySevenCQ_19971689923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 925107929942445773) ^ 462553964971222886 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 925107929942445773) ^ 7284314408995636 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 925107929942445773) ^ 10145618480884 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 925107929942445773) ^ 46320964 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_988581234453477779 : Nat.Prime 988581234453477779 := by
  apply lucas_primality 988581234453477779 (2 : ZMod 988581234453477779)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (7151, 1), (270667, 1), (8806073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (7151, 1), (270667, 1), (8806073, 1)] : List FactorBlock).map factorBlockValue).prod) = 988581234453477779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_29
      · exact prime_ninetySevenCQ_7151
      · exact prime_ninetySevenCQ_270667
      · exact prime_ninetySevenCQ_8806073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 988581234453477779) ^ 494290617226738889 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 988581234453477779) ^ 34089008084602682 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 988581234453477779) ^ 138243774920078 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 988581234453477779) ^ 3652389225334 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 988581234453477779) ^ 112261303586 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2304522874688847259 : Nat.Prime 2304522874688847259 := by
  apply lucas_primality 2304522874688847259 (2 : ZMod 2304522874688847259)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (5409678109598233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (5409678109598233, 1)] : List FactorBlock).map factorBlockValue).prod) = 2304522874688847259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_71
      · exact prime_ninetySevenCQ_5409678109598233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2304522874688847259) ^ 1152261437344423629 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2304522874688847259) ^ 768174291562949086 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2304522874688847259) ^ 32458068657589398 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2304522874688847259) ^ 426 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2338348104614138237 : Nat.Prime 2338348104614138237 := by
  apply lucas_primality 2338348104614138237 (2 : ZMod 2338348104614138237)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (211, 1), (251, 1), (14389, 1), (12575711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (211, 1), (251, 1), (14389, 1), (12575711, 1)] : List FactorBlock).map factorBlockValue).prod) = 2338348104614138237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_61
      · exact prime_ninetySevenCQ_211
      · exact prime_ninetySevenCQ_251
      · exact prime_ninetySevenCQ_14389
      · exact prime_ninetySevenCQ_12575711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2338348104614138237) ^ 1169174052307069118 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2338348104614138237) ^ 38333575485477676 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2338348104614138237) ^ 11082218505280276 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2338348104614138237) ^ 9316127906829236 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2338348104614138237) ^ 162509424186124 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2338348104614138237) ^ 185941622276 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_4330373662105114571 : Nat.Prime 4330373662105114571 := by
  apply lucas_primality 4330373662105114571 (2 : ZMod 4330373662105114571)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2415871, 1), (179246891167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2415871, 1), (179246891167, 1)] : List FactorBlock).map factorBlockValue).prod) = 4330373662105114571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_2415871
      · exact prime_ninetySevenCQ_179246891167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4330373662105114571) ^ 2165186831052557285 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4330373662105114571) ^ 866074732421022914 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4330373662105114571) ^ 1792468911670 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4330373662105114571) ^ 24158710 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_24690329136096804517 : Nat.Prime 24690329136096804517 := by
  apply lucas_primality 24690329136096804517 (5 : ZMod 24690329136096804517)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (67, 1), (157, 1), (27943006912771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (67, 1), (157, 1), (27943006912771, 1)] : List FactorBlock).map factorBlockValue).prod) = 24690329136096804517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_67
      · exact prime_ninetySevenCQ_157
      · exact prime_ninetySevenCQ_27943006912771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 24690329136096804517) ^ 12345164568048402258 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 24690329136096804517) ^ 8230109712032268172 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 24690329136096804517) ^ 3527189876585257788 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 24690329136096804517) ^ 368512375165623948 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 24690329136096804517) ^ 157263242905075188 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 24690329136096804517) ^ 883596 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_42012142050658011587 : Nat.Prime 42012142050658011587 := by
  apply lucas_primality 42012142050658011587 (2 : ZMod 42012142050658011587)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1063, 1), (2129, 1), (2837, 1), (3271723307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1063, 1), (2129, 1), (2837, 1), (3271723307, 1)] : List FactorBlock).map factorBlockValue).prod) = 42012142050658011587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_1063
      · exact prime_ninetySevenCQ_2129
      · exact prime_ninetySevenCQ_2837
      · exact prime_ninetySevenCQ_3271723307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42012142050658011587) ^ 21006071025329005793 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42012142050658011587) ^ 39522240875501422 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42012142050658011587) ^ 19733274800684834 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42012142050658011587) ^ 14808650705201978 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42012142050658011587) ^ 12840982598 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_98761316544387218069 : Nat.Prime 98761316544387218069 := by
  apply lucas_primality 98761316544387218069 (2 : ZMod 98761316544387218069)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (24690329136096804517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (24690329136096804517, 1)] : List FactorBlock).map factorBlockValue).prod) = 98761316544387218069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_24690329136096804517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 98761316544387218069) ^ 49380658272193609034 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 98761316544387218069) ^ 4 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_106265533810697062849 : Nat.Prime 106265533810697062849 := by
  apply lucas_primality 106265533810697062849 (7 : ZMod 106265533810697062849)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (43, 1), (67, 1), (103, 1), (1223, 1), (1259, 1), (134591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (43, 1), (67, 1), (103, 1), (1223, 1), (1259, 1), (134591, 1)] : List FactorBlock).map factorBlockValue).prod) = 106265533810697062849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_43
      · exact prime_ninetySevenCQ_67
      · exact prime_ninetySevenCQ_103
      · exact prime_ninetySevenCQ_1223
      · exact prime_ninetySevenCQ_1259
      · exact prime_ninetySevenCQ_134591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 106265533810697062849) ^ 53132766905348531424 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 106265533810697062849) ^ 35421844603565687616 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 106265533810697062849) ^ 2471291483969699136 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 106265533810697062849) ^ 1586052743443239744 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 106265533810697062849) ^ 1031704211754340416 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 106265533810697062849) ^ 86889234514061376 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 106265533810697062849) ^ 84404713114135872 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 106265533810697062849) ^ 789544128587328 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_135444897923855599153 : Nat.Prime 135444897923855599153 := by
  apply lucas_primality 135444897923855599153 (5 : ZMod 135444897923855599153)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (59, 1), (751, 1), (1307, 1), (7589, 1), (2140169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (59, 1), (751, 1), (1307, 1), (7589, 1), (2140169, 1)] : List FactorBlock).map factorBlockValue).prod) = 135444897923855599153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_59
      · exact prime_ninetySevenCQ_751
      · exact prime_ninetySevenCQ_1307
      · exact prime_ninetySevenCQ_7589
      · exact prime_ninetySevenCQ_2140169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 135444897923855599153) ^ 67722448961927799576 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 135444897923855599153) ^ 45148299307951866384 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 135444897923855599153) ^ 2295676235997552528 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 135444897923855599153) ^ 180352726929235152 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 135444897923855599153) ^ 103630373315880336 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 135444897923855599153) ^ 17847529045177968 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 135444897923855599153) ^ 63287010476208 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_203697248571950914259 : Nat.Prime 203697248571950914259 := by
  apply lucas_primality 203697248571950914259 (2 : ZMod 203697248571950914259)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (317, 1), (2729, 1), (704978541859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (317, 1), (2729, 1), (704978541859, 1)] : List FactorBlock).map factorBlockValue).prod) = 203697248571950914259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_167
      · exact prime_ninetySevenCQ_317
      · exact prime_ninetySevenCQ_2729
      · exact prime_ninetySevenCQ_704978541859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 203697248571950914259) ^ 101848624285975457129 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 203697248571950914259) ^ 1219744003424855774 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 203697248571950914259) ^ 642578071204892474 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 203697248571950914259) ^ 74641718054947202 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 203697248571950914259) ^ 288941062 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_205137776443232917331 : Nat.Prime 205137776443232917331 := by
  apply lucas_primality 205137776443232917331 (2 : ZMod 205137776443232917331)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1697, 1), (4484743, 1), (2695418723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1697, 1), (4484743, 1), (2695418723, 1)] : List FactorBlock).map factorBlockValue).prod) = 205137776443232917331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_1697
      · exact prime_ninetySevenCQ_4484743
      · exact prime_ninetySevenCQ_2695418723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 205137776443232917331) ^ 102568888221616458665 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 205137776443232917331) ^ 41027555288646583466 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 205137776443232917331) ^ 120882602500431890 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 205137776443232917331) ^ 45741255729310 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 205137776443232917331) ^ 76106088710 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_259506809220435701381 : Nat.Prime 259506809220435701381 := by
  apply lucas_primality 259506809220435701381 (2 : ZMod 259506809220435701381)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2039, 1), (212437, 1), (29955141583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2039, 1), (212437, 1), (29955141583, 1)] : List FactorBlock).map factorBlockValue).prod) = 259506809220435701381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_2039
      · exact prime_ninetySevenCQ_212437
      · exact prime_ninetySevenCQ_29955141583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 259506809220435701381) ^ 129753404610217850690 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 259506809220435701381) ^ 51901361844087140276 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 259506809220435701381) ^ 127271608249355420 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 259506809220435701381) ^ 1221570673754740 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 259506809220435701381) ^ 8663180860 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_268577163723201496951 : Nat.Prime 268577163723201496951 := by
  apply lucas_primality 268577163723201496951 (6 : ZMod 268577163723201496951)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (443, 1), (1483, 1), (2725416914377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (443, 1), (1483, 1), (2725416914377, 1)] : List FactorBlock).map factorBlockValue).prod) = 268577163723201496951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_443
      · exact prime_ninetySevenCQ_1483
      · exact prime_ninetySevenCQ_2725416914377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 268577163723201496951) ^ 134288581861600748475 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 268577163723201496951) ^ 89525721241067165650 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 268577163723201496951) ^ 53715432744640299390 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 268577163723201496951) ^ 606268992603163650 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 268577163723201496951) ^ 181103953960351650 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 268577163723201496951) ^ 98545350 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_336097136405264092697 : Nat.Prime 336097136405264092697 := by
  apply lucas_primality 336097136405264092697 (3 : ZMod 336097136405264092697)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (42012142050658011587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (42012142050658011587, 1)] : List FactorBlock).map factorBlockValue).prod) = 336097136405264092697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_42012142050658011587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 336097136405264092697) ^ 168048568202632046348 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 336097136405264092697) ^ 8 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_380584191591041053793 : Nat.Prime 380584191591041053793 := by
  apply lucas_primality 380584191591041053793 (3 : ZMod 380584191591041053793)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (23, 1), (4642081, 1), (10126690367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (23, 1), (4642081, 1), (10126690367, 1)] : List FactorBlock).map factorBlockValue).prod) = 380584191591041053793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_23
      · exact prime_ninetySevenCQ_4642081
      · exact prime_ninetySevenCQ_10126690367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 380584191591041053793) ^ 190292095795520526896 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 380584191591041053793) ^ 34598562871912823072 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 380584191591041053793) ^ 16547138764827871904 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 380584191591041053793) ^ 81985685211232 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 380584191591041053793) ^ 37582287776 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_400549702816222292633 : Nat.Prime 400549702816222292633 := by
  apply lucas_primality 400549702816222292633 (3 : ZMod 400549702816222292633)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (109, 1), (42727, 1), (826978418381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (109, 1), (42727, 1), (826978418381, 1)] : List FactorBlock).map factorBlockValue).prod) = 400549702816222292633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_109
      · exact prime_ninetySevenCQ_42727
      · exact prime_ninetySevenCQ_826978418381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 400549702816222292633) ^ 200274851408111146316 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 400549702816222292633) ^ 30811515601247868664 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 400549702816222292633) ^ 3674767915745158648 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 400549702816222292633) ^ 9374627350767016 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 400549702816222292633) ^ 484353272 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_452722924424520323243 : Nat.Prime 452722924424520323243 := by
  apply lucas_primality 452722924424520323243 (2 : ZMod 452722924424520323243)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (689174281, 1), (328453148141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (689174281, 1), (328453148141, 1)] : List FactorBlock).map factorBlockValue).prod) = 452722924424520323243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_689174281
      · exact prime_ninetySevenCQ_328453148141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 452722924424520323243) ^ 226361462212260161621 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 452722924424520323243) ^ 656906296282 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 452722924424520323243) ^ 1378348562 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_636579428229403127149 : Nat.Prime 636579428229403127149 := by
  apply lucas_primality 636579428229403127149 (6 : ZMod 636579428229403127149)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (124882273, 1), (7199768747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (124882273, 1), (7199768747, 1)] : List FactorBlock).map factorBlockValue).prod) = 636579428229403127149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_59
      · exact prime_ninetySevenCQ_124882273
      · exact prime_ninetySevenCQ_7199768747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 636579428229403127149) ^ 318289714114701563574 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 636579428229403127149) ^ 212193142743134375716 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 636579428229403127149) ^ 10789481834396663172 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 636579428229403127149) ^ 5097436272876 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 636579428229403127149) ^ 88416649284 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_861529814594919634159 : Nat.Prime 861529814594919634159 := by
  apply lucas_primality 861529814594919634159 (3 : ZMod 861529814594919634159)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (157, 1), (3032417, 1), (33511045433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (157, 1), (3032417, 1), (33511045433, 1)] : List FactorBlock).map factorBlockValue).prod) = 861529814594919634159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_157
      · exact prime_ninetySevenCQ_3032417
      · exact prime_ninetySevenCQ_33511045433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 861529814594919634159) ^ 430764907297459817079 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 861529814594919634159) ^ 287176604864973211386 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 861529814594919634159) ^ 5487451048375284294 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 861529814594919634159) ^ 284106643180974 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 861529814594919634159) ^ 25708831326 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1074235353674386606597 : Nat.Prime 1074235353674386606597 := by
  apply lucas_primality 1074235353674386606597 (2 : ZMod 1074235353674386606597)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5181101, 1), (5759368700861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5181101, 1), (5759368700861, 1)] : List FactorBlock).map factorBlockValue).prod) = 1074235353674386606597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5181101
      · exact prime_ninetySevenCQ_5759368700861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1074235353674386606597) ^ 537117676837193303298 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1074235353674386606597) ^ 358078451224795535532 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1074235353674386606597) ^ 207337273230996 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1074235353674386606597) ^ 186519636 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1633480813824266132581 : Nat.Prime 1633480813824266132581 := by
  apply lucas_primality 1633480813824266132581 (10 : ZMod 1633480813824266132581)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (43, 1), (89, 1), (179, 1), (673, 1), (743, 1), (2309, 1), (34421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (43, 1), (89, 1), (179, 1), (673, 1), (743, 1), (2309, 1), (34421, 1)] : List FactorBlock).map factorBlockValue).prod) = 1633480813824266132581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_43
      · exact prime_ninetySevenCQ_89
      · exact prime_ninetySevenCQ_179
      · exact prime_ninetySevenCQ_673
      · exact prime_ninetySevenCQ_743
      · exact prime_ninetySevenCQ_2309
      · exact prime_ninetySevenCQ_34421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1633480813824266132581) ^ 816740406912133066290 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1633480813824266132581) ^ 544493604608088710860 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1633480813824266132581) ^ 326696162764853226516 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1633480813824266132581) ^ 37987925902889910060 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1633480813824266132581) ^ 18353717009261417220 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1633480813824266132581) ^ 9125591138683051020 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1633480813824266132581) ^ 2427163170615551460 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1633480813824266132581) ^ 2198493692899416060 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1633480813824266132581) ^ 707440802868889620 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1633480813824266132581) ^ 47455937184400980 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2405939490771829936093 : Nat.Prime 2405939490771829936093 := by
  apply lucas_primality 2405939490771829936093 (5 : ZMod 2405939490771829936093)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (8101, 1), (634600215751519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (8101, 1), (634600215751519, 1)] : List FactorBlock).map factorBlockValue).prod) = 2405939490771829936093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_8101
      · exact prime_ninetySevenCQ_634600215751519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2405939490771829936093) ^ 1202969745385914968046 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2405939490771829936093) ^ 801979830257276645364 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2405939490771829936093) ^ 185072268520909995084 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2405939490771829936093) ^ 296992900971710892 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2405939490771829936093) ^ 3791268 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2784549063058874689211 : Nat.Prime 2784549063058874689211 := by
  apply lucas_primality 2784549063058874689211 (2 : ZMod 2784549063058874689211)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (14437, 1), (470428972822013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (14437, 1), (470428972822013, 1)] : List FactorBlock).map factorBlockValue).prod) = 2784549063058874689211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_41
      · exact prime_ninetySevenCQ_14437
      · exact prime_ninetySevenCQ_470428972822013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2784549063058874689211) ^ 1392274531529437344605 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2784549063058874689211) ^ 556909812611774937842 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2784549063058874689211) ^ 67915830806314016810 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2784549063058874689211) ^ 192875878857025330 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2784549063058874689211) ^ 5919170 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_3209389644407053061791 : Nat.Prime 3209389644407053061791 := by
  apply lucas_primality 3209389644407053061791 (3 : ZMod 3209389644407053061791)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (61, 1), (53144388879070261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (61, 1), (53144388879070261, 1)] : List FactorBlock).map factorBlockValue).prod) = 3209389644407053061791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_61
      · exact prime_ninetySevenCQ_53144388879070261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3209389644407053061791) ^ 1604694822203526530895 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3209389644407053061791) ^ 1069796548135684353930 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3209389644407053061791) ^ 641877928881410612358 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3209389644407053061791) ^ 291762694946095732890 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3209389644407053061791) ^ 52612944990279558390 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3209389644407053061791) ^ 60390 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_6166082628059992727833 : Nat.Prime 6166082628059992727833 := by
  apply lucas_primality 6166082628059992727833 (5 : ZMod 6166082628059992727833)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (190667219, 1), (449159729449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (190667219, 1), (449159729449, 1)] : List FactorBlock).map factorBlockValue).prod) = 6166082628059992727833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_190667219
      · exact prime_ninetySevenCQ_449159729449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6166082628059992727833) ^ 3083041314029996363916 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6166082628059992727833) ^ 2055360876019997575944 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6166082628059992727833) ^ 32339500520328 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6166082628059992727833) ^ 13728039768 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_6338120941943284525403 : Nat.Prime 6338120941943284525403 := by
  apply lucas_primality 6338120941943284525403 (2 : ZMod 6338120941943284525403)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (452722924424520323243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (452722924424520323243, 1)] : List FactorBlock).map factorBlockValue).prod) = 6338120941943284525403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_452722924424520323243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6338120941943284525403) ^ 3169060470971642262701 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6338120941943284525403) ^ 905445848849040646486 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6338120941943284525403) ^ 14 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_11217974891194807910441 : Nat.Prime 11217974891194807910441 := by
  apply lucas_primality 11217974891194807910441 (13 : ZMod 11217974891194807910441)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (1281433, 1), (31265150842831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (1281433, 1), (31265150842831, 1)] : List FactorBlock).map factorBlockValue).prod) = 11217974891194807910441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_1281433
      · exact prime_ninetySevenCQ_31265150842831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 11217974891194807910441) ^ 5608987445597403955220 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 11217974891194807910441) ^ 2243594978238961582088 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 11217974891194807910441) ^ 1602567841599258272920 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 11217974891194807910441) ^ 8754242235992680 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (13 : ZMod 11217974891194807910441) ^ 358801240 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_29589456915787305250999 : Nat.Prime 29589456915787305250999 := by
  apply lucas_primality 29589456915787305250999 (3 : ZMod 29589456915787305250999)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (37, 1), (2338348104614138237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (37, 1), (2338348104614138237, 1)] : List FactorBlock).map factorBlockValue).prod) = 29589456915787305250999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_37
      · exact prime_ninetySevenCQ_2338348104614138237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29589456915787305250999) ^ 14794728457893652625499 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 29589456915787305250999) ^ 9863152305262435083666 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 29589456915787305250999) ^ 1557339837673016065842 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 29589456915787305250999) ^ 799715051778035277054 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 29589456915787305250999) ^ 12654 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_124723768077485613737249 : Nat.Prime 124723768077485613737249 := by
  apply lucas_primality 124723768077485613737249 (3 : ZMod 124723768077485613737249)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (205137776443232917331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (205137776443232917331, 1)] : List FactorBlock).map factorBlockValue).prod) = 124723768077485613737249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_205137776443232917331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 124723768077485613737249) ^ 62361884038742806868624 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 124723768077485613737249) ^ 6564408846183453354592 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 124723768077485613737249) ^ 608 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_140508083704542839506729 : Nat.Prime 140508083704542839506729 := by
  apply lucas_primality 140508083704542839506729 (22 : ZMod 140508083704542839506729)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (13, 1), (131, 1), (3499, 1), (109166395082939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (13, 1), (131, 1), (3499, 1), (109166395082939, 1)] : List FactorBlock).map factorBlockValue).prod) = 140508083704542839506729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_131
      · exact prime_ninetySevenCQ_3499
      · exact prime_ninetySevenCQ_109166395082939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 140508083704542839506729) ^ 70254041852271419753364 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (22 : ZMod 140508083704542839506729) ^ 46836027901514279835576 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (22 : ZMod 140508083704542839506729) ^ 10808314131118679962056 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (22 : ZMod 140508083704542839506729) ^ 1072580791637731599288 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (22 : ZMod 140508083704542839506729) ^ 40156640098468945272 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (22 : ZMod 140508083704542839506729) ^ 1287100152 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_227120368680755302217341 : Nat.Prime 227120368680755302217341 := by
  apply lucas_primality 227120368680755302217341 (2 : ZMod 227120368680755302217341)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (67, 1), (181, 1), (312141459389180207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (67, 1), (181, 1), (312141459389180207, 1)] : List FactorBlock).map factorBlockValue).prod) = 227120368680755302217341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_67
      · exact prime_ninetySevenCQ_181
      · exact prime_ninetySevenCQ_312141459389180207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 227120368680755302217341) ^ 113560184340377651108670 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 227120368680755302217341) ^ 75706789560251767405780 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 227120368680755302217341) ^ 45424073736151060443468 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 227120368680755302217341) ^ 3389856248966497048020 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 227120368680755302217341) ^ 1254808666744504432140 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 227120368680755302217341) ^ 727620 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_256622302437721310656061 : Nat.Prime 256622302437721310656061 := by
  apply lucas_primality 256622302437721310656061 (7 : ZMod 256622302437721310656061)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (47, 1), (4721, 1), (20543, 1), (64919, 1), (3941887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (47, 1), (4721, 1), (20543, 1), (64919, 1), (3941887, 1)] : List FactorBlock).map factorBlockValue).prod) = 256622302437721310656061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_47
      · exact prime_ninetySevenCQ_4721
      · exact prime_ninetySevenCQ_20543
      · exact prime_ninetySevenCQ_64919
      · exact prime_ninetySevenCQ_3941887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 256622302437721310656061) ^ 128311151218860655328030 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 256622302437721310656061) ^ 51324460487544262131212 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 256622302437721310656061) ^ 23329300221611028241460 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 256622302437721310656061) ^ 5460048988036623630980 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 256622302437721310656061) ^ 54357615428451876860 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 256622302437721310656061) ^ 12491958449969396420 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 256622302437721310656061) ^ 3952961420196264740 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 256622302437721310656061) ^ 65101384803197380 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_289921471749753573456541 : Nat.Prime 289921471749753573456541 := by
  apply lucas_primality 289921471749753573456541 (2 : ZMod 289921471749753573456541)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (11, 1), (4271, 1), (20825647, 1), (548739043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (11, 1), (4271, 1), (20825647, 1), (548739043, 1)] : List FactorBlock).map factorBlockValue).prod) = 289921471749753573456541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_4271
      · exact prime_ninetySevenCQ_20825647
      · exact prime_ninetySevenCQ_548739043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 289921471749753573456541) ^ 144960735874876786728270 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 289921471749753573456541) ^ 96640490583251191152180 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 289921471749753573456541) ^ 57984294349950714691308 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 289921471749753573456541) ^ 26356497431795779405140 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 289921471749753573456541) ^ 67881402891536776740 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 289921471749753573456541) ^ 13921366848758820 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 289921471749753573456541) ^ 528341249721780 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_311156630556690293978191 : Nat.Prime 311156630556690293978191 := by
  apply lucas_primality 311156630556690293978191 (7 : ZMod 311156630556690293978191)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 3), (509, 1), (1249, 1), (2083, 1), (22834641337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 3), (509, 1), (1249, 1), (2083, 1), (22834641337, 1)] : List FactorBlock).map factorBlockValue).prod) = 311156630556690293978191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_509
      · exact prime_ninetySevenCQ_1249
      · exact prime_ninetySevenCQ_2083
      · exact prime_ninetySevenCQ_22834641337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 311156630556690293978191) ^ 155578315278345146989095 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 311156630556690293978191) ^ 103718876852230097992730 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 311156630556690293978191) ^ 62231326111338058795638 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 311156630556690293978191) ^ 44450947222384327711170 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 311156630556690293978191) ^ 611309686751847335910 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 311156630556690293978191) ^ 249124604128655159310 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 311156630556690293978191) ^ 149379083320542627930 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (7 : ZMod 311156630556690293978191) ^ 13626517095870 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_420755613533953539071101 : Nat.Prime 420755613533953539071101 := by
  apply lucas_primality 420755613533953539071101 (2 : ZMod 420755613533953539071101)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 1), (744576457, 1), (144895871657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 1), (744576457, 1), (144895871657, 1)] : List FactorBlock).map factorBlockValue).prod) = 420755613533953539071101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_13
      · exact prime_ninetySevenCQ_744576457
      · exact prime_ninetySevenCQ_144895871657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 420755613533953539071101) ^ 210377806766976769535550 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 420755613533953539071101) ^ 140251871177984513023700 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 420755613533953539071101) ^ 84151122706790707814220 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 420755613533953539071101) ^ 32365816425688733774700 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 420755613533953539071101) ^ 565093899462300 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 420755613533953539071101) ^ 2903848182300 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_513244604875442621312123 : Nat.Prime 513244604875442621312123 := by
  apply lucas_primality 513244604875442621312123 (2 : ZMod 513244604875442621312123)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (256622302437721310656061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (256622302437721310656061, 1)] : List FactorBlock).map factorBlockValue).prod) = 513244604875442621312123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_256622302437721310656061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 513244604875442621312123) ^ 256622302437721310656061 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 513244604875442621312123) ^ 2 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_565106500889318130182581 : Nat.Prime 565106500889318130182581 := by
  apply lucas_primality 565106500889318130182581 (6 : ZMod 565106500889318130182581)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (71, 1), (239, 1), (28631, 1), (2769416314891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (71, 1), (239, 1), (28631, 1), (2769416314891, 1)] : List FactorBlock).map factorBlockValue).prod) = 565106500889318130182581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_71
      · exact prime_ninetySevenCQ_239
      · exact prime_ninetySevenCQ_28631
      · exact prime_ninetySevenCQ_2769416314891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 565106500889318130182581) ^ 282553250444659065091290 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 565106500889318130182581) ^ 188368833629772710060860 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 565106500889318130182581) ^ 113021300177863626036516 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 565106500889318130182581) ^ 80729500127045447168940 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 565106500889318130182581) ^ 7959246491398846903980 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 565106500889318130182581) ^ 2364462346817230670220 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 565106500889318130182581) ^ 19737574687901859180 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (6 : ZMod 565106500889318130182581) ^ 204052564380 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_771159414959039847412781 : Nat.Prime 771159414959039847412781 := by
  apply lucas_primality 771159414959039847412781 (2 : ZMod 771159414959039847412781)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1945057, 1), (19823568537041327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1945057, 1), (19823568537041327, 1)] : List FactorBlock).map factorBlockValue).prod) = 771159414959039847412781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_1945057
      · exact prime_ninetySevenCQ_19823568537041327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 771159414959039847412781) ^ 385579707479519923706390 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 771159414959039847412781) ^ 154231882991807969482556 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 771159414959039847412781) ^ 396471370740826540 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 771159414959039847412781) ^ 38901140 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1239005680308279940670737 : Nat.Prime 1239005680308279940670737 := by
  apply lucas_primality 1239005680308279940670737 (5 : ZMod 1239005680308279940670737)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (139, 1), (159167, 1), (6559337, 1), (9361613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (139, 1), (159167, 1), (6559337, 1), (9361613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1239005680308279940670737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_19
      · exact prime_ninetySevenCQ_139
      · exact prime_ninetySevenCQ_159167
      · exact prime_ninetySevenCQ_6559337
      · exact prime_ninetySevenCQ_9361613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1239005680308279940670737) ^ 619502840154139970335368 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1239005680308279940670737) ^ 413001893436093313556912 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1239005680308279940670737) ^ 65210825279383154772144 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1239005680308279940670737) ^ 8913709930275395256624 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1239005680308279940670737) ^ 7784312579292692208 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1239005680308279940670737) ^ 188891907872438928 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1239005680308279940670737) ^ 132349594061224272 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1362722212084531813304047 : Nat.Prime 1362722212084531813304047 := by
  apply lucas_primality 1362722212084531813304047 (3 : ZMod 1362722212084531813304047)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (227120368680755302217341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (227120368680755302217341, 1)] : List FactorBlock).map factorBlockValue).prod) = 1362722212084531813304047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_227120368680755302217341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1362722212084531813304047) ^ 681361106042265906652023 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1362722212084531813304047) ^ 454240737361510604434682 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1362722212084531813304047) ^ 6 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1769423683237267400305531 : Nat.Prime 1769423683237267400305531 := by
  apply lucas_primality 1769423683237267400305531 (2 : ZMod 1769423683237267400305531)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (89, 1), (431, 1), (107260333, 1), (843247849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (89, 1), (431, 1), (107260333, 1), (843247849, 1)] : List FactorBlock).map factorBlockValue).prod) = 1769423683237267400305531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_89
      · exact prime_ninetySevenCQ_431
      · exact prime_ninetySevenCQ_107260333
      · exact prime_ninetySevenCQ_843247849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1769423683237267400305531) ^ 884711841618633700152765 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769423683237267400305531) ^ 589807894412422466768510 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769423683237267400305531) ^ 353884736647453480061106 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769423683237267400305531) ^ 104083746072780435312090 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769423683237267400305531) ^ 19881164980194015733770 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769423683237267400305531) ^ 4105391376420574014630 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769423683237267400305531) ^ 16496533562293410 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769423683237267400305531) ^ 2098343547908970 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1801783053009894651027559 : Nat.Prime 1801783053009894651027559 := by
  apply lucas_primality 1801783053009894651027559 (3 : ZMod 1801783053009894651027559)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6691403, 1), (44878058532963731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6691403, 1), (44878058532963731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1801783053009894651027559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_6691403
      · exact prime_ninetySevenCQ_44878058532963731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1801783053009894651027559) ^ 900891526504947325513779 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1801783053009894651027559) ^ 600594351003298217009186 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1801783053009894651027559) ^ 269268351197782386 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1801783053009894651027559) ^ 40148418 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2164751732066856213164491 : Nat.Prime 2164751732066856213164491 := by
  apply lucas_primality 2164751732066856213164491 (2 : ZMod 2164751732066856213164491)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (29, 1), (571, 1), (76781, 1), (18918108683059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (29, 1), (571, 1), (76781, 1), (18918108683059, 1)] : List FactorBlock).map factorBlockValue).prod) = 2164751732066856213164491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_29
      · exact prime_ninetySevenCQ_571
      · exact prime_ninetySevenCQ_76781
      · exact prime_ninetySevenCQ_18918108683059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2164751732066856213164491) ^ 1082375866033428106582245 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2164751732066856213164491) ^ 721583910688952071054830 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2164751732066856213164491) ^ 432950346413371242632898 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2164751732066856213164491) ^ 74646611450581248729810 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2164751732066856213164491) ^ 3791158900292217536190 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2164751732066856213164491) ^ 28193846551449658290 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2164751732066856213164491) ^ 114427492110 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_4624561971044994545874751 : Nat.Prime 4624561971044994545874751 := by
  apply lucas_primality 4624561971044994545874751 (3 : ZMod 4624561971044994545874751)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (6166082628059992727833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (6166082628059992727833, 1)] : List FactorBlock).map factorBlockValue).prod) = 4624561971044994545874751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_6166082628059992727833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4624561971044994545874751) ^ 2312280985522497272937375 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4624561971044994545874751) ^ 1541520657014998181958250 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4624561971044994545874751) ^ 924912394208998909174950 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4624561971044994545874751) ^ 750 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_10739828409624815016726173 : Nat.Prime 10739828409624815016726173 := by
  apply lucas_primality 10739828409624815016726173 (2 : ZMod 10739828409624815016726173)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1423, 1), (4483, 1), (420885256131377827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1423, 1), (4483, 1), (420885256131377827, 1)] : List FactorBlock).map factorBlockValue).prod) = 10739828409624815016726173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_1423
      · exact prime_ninetySevenCQ_4483
      · exact prime_ninetySevenCQ_420885256131377827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10739828409624815016726173) ^ 5369914204812407508363086 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10739828409624815016726173) ^ 7547314412947867193764 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10739828409624815016726173) ^ 2395678877899802591284 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10739828409624815016726173) ^ 25517236 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_22363472651710954514157971 : Nat.Prime 22363472651710954514157971 := by
  apply lucas_primality 22363472651710954514157971 (2 : ZMod 22363472651710954514157971)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1483, 1), (18617, 1), (81000629293497527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1483, 1), (18617, 1), (81000629293497527, 1)] : List FactorBlock).map factorBlockValue).prod) = 22363472651710954514157971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_1483
      · exact prime_ninetySevenCQ_18617
      · exact prime_ninetySevenCQ_81000629293497527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22363472651710954514157971) ^ 11181736325855477257078985 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22363472651710954514157971) ^ 4472694530342190902831594 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22363472651710954514157971) ^ 15079887155570434601590 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22363472651710954514157971) ^ 1201239332422568325410 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22363472651710954514157971) ^ 276090110 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_45507891967449910614524633 : Nat.Prime 45507891967449910614524633 := by
  apply lucas_primality 45507891967449910614524633 (3 : ZMod 45507891967449910614524633)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (181, 1), (8623, 1), (125651, 1), (29006399301883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (181, 1), (8623, 1), (125651, 1), (29006399301883, 1)] : List FactorBlock).map factorBlockValue).prod) = 45507891967449910614524633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_181
      · exact prime_ninetySevenCQ_8623
      · exact prime_ninetySevenCQ_125651
      · exact prime_ninetySevenCQ_29006399301883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45507891967449910614524633) ^ 22753945983724955307262316 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 45507891967449910614524633) ^ 251424817499723263063672 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 45507891967449910614524633) ^ 5277501097929944406184 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 45507891967449910614524633) ^ 362176918348838533832 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 45507891967449910614524633) ^ 1568891453704 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_92483780449978850603711351 : Nat.Prime 92483780449978850603711351 := by
  apply lucas_primality 92483780449978850603711351 (22 : ZMod 92483780449978850603711351)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (31, 1), (61, 1), (233, 1), (6079, 1), (690583148342071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (31, 1), (61, 1), (233, 1), (6079, 1), (690583148342071, 1)] : List FactorBlock).map factorBlockValue).prod) = 92483780449978850603711351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_31
      · exact prime_ninetySevenCQ_61
      · exact prime_ninetySevenCQ_233
      · exact prime_ninetySevenCQ_6079
      · exact prime_ninetySevenCQ_690583148342071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 92483780449978850603711351) ^ 46241890224989425301855675 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (22 : ZMod 92483780449978850603711351) ^ 18496756089995770120742270 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (22 : ZMod 92483780449978850603711351) ^ 2983347756450930664635850 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (22 : ZMod 92483780449978850603711351) ^ 1516127548360309026290350 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (22 : ZMod 92483780449978850603711351) ^ 396926096351840560530950 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (22 : ZMod 92483780449978850603711351) ^ 15213650345448075440650 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (22 : ZMod 92483780449978850603711351) ^ 133921281850 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_123444443227097712323575969 : Nat.Prime 123444443227097712323575969 := by
  apply lucas_primality 123444443227097712323575969 (11 : ZMod 123444443227097712323575969)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (24007, 1), (168769, 1), (317372828660401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (24007, 1), (168769, 1), (317372828660401, 1)] : List FactorBlock).map factorBlockValue).prod) = 123444443227097712323575969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_24007
      · exact prime_ninetySevenCQ_168769
      · exact prime_ninetySevenCQ_317372828660401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 123444443227097712323575969) ^ 61722221613548856161787984 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 123444443227097712323575969) ^ 41148147742365904107858656 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 123444443227097712323575969) ^ 5142018712337972771424 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 123444443227097712323575969) ^ 731440271774423693472 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (11 : ZMod 123444443227097712323575969) ^ 388957188768 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_292550734076463711093372641 : Nat.Prime 292550734076463711093372641 := by
  apply lucas_primality 292550734076463711093372641 (3 : ZMod 292550734076463711093372641)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (113, 1), (4490411789, 1), (3603434204647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (113, 1), (4490411789, 1), (3603434204647, 1)] : List FactorBlock).map factorBlockValue).prod) = 292550734076463711093372641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_113
      · exact prime_ninetySevenCQ_4490411789
      · exact prime_ninetySevenCQ_3603434204647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 292550734076463711093372641) ^ 146275367038231855546686320 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 292550734076463711093372641) ^ 58510146815292742218674528 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 292550734076463711093372641) ^ 2588944549349236381357280 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 292550734076463711093372641) ^ 65150090420017760 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 292550734076463711093372641) ^ 81186645145120 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_423173017557098799810339761 : Nat.Prime 423173017557098799810339761 := by
  apply lucas_primality 423173017557098799810339761 (3 : ZMod 423173017557098799810339761)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (17, 1), (311156630556690293978191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (17, 1), (311156630556690293978191, 1)] : List FactorBlock).map factorBlockValue).prod) = 423173017557098799810339761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_17
      · exact prime_ninetySevenCQ_311156630556690293978191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 423173017557098799810339761) ^ 211586508778549399905169880 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 423173017557098799810339761) ^ 84634603511419759962067952 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 423173017557098799810339761) ^ 24892530444535223518255280 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 423173017557098799810339761) ^ 1360 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_910157839348998212290492661 : Nat.Prime 910157839348998212290492661 := by
  apply lucas_primality 910157839348998212290492661 (3 : ZMod 910157839348998212290492661)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (45507891967449910614524633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (45507891967449910614524633, 1)] : List FactorBlock).map factorBlockValue).prod) = 910157839348998212290492661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_45507891967449910614524633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 910157839348998212290492661) ^ 455078919674499106145246330 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 910157839348998212290492661) ^ 182031567869799642458098532 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 910157839348998212290492661) ^ 20 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1398535216560655789617098479 : Nat.Prime 1398535216560655789617098479 := by
  apply lucas_primality 1398535216560655789617098479 (3 : ZMod 1398535216560655789617098479)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (149873, 1), (827147, 1), (1506551, 1), (5136011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (149873, 1), (827147, 1), (1506551, 1), (5136011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1398535216560655789617098479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_149873
      · exact prime_ninetySevenCQ_827147
      · exact prime_ninetySevenCQ_1506551
      · exact prime_ninetySevenCQ_5136011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1398535216560655789617098479) ^ 699267608280327894808549239 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398535216560655789617098479) ^ 466178405520218596539032826 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398535216560655789617098479) ^ 9331468753949382407886 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398535216560655789617098479) ^ 1690794038496973076874 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398535216560655789617098479) ^ 928302604133982712578 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398535216560655789617098479) ^ 272299887317347215498 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_1737574056938996587100031443 : Nat.Prime 1737574056938996587100031443 := by
  apply lucas_primality 1737574056938996587100031443 (2 : ZMod 1737574056938996587100031443)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (491, 1), (1769423683237267400305531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (491, 1), (1769423683237267400305531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1737574056938996587100031443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_491
      · exact prime_ninetySevenCQ_1769423683237267400305531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1737574056938996587100031443) ^ 868787028469498293550015721 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1737574056938996587100031443) ^ 3538847366474534800611062 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1737574056938996587100031443) ^ 982 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_2730473518046994636871477981 : Nat.Prime 2730473518046994636871477981 := by
  apply lucas_primality 2730473518046994636871477981 (2 : ZMod 2730473518046994636871477981)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (45507891967449910614524633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (45507891967449910614524633, 1)] : List FactorBlock).map factorBlockValue).prod) = 2730473518046994636871477981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_5
      · exact prime_ninetySevenCQ_45507891967449910614524633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2730473518046994636871477981) ^ 1365236759023497318435738990 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2730473518046994636871477981) ^ 910157839348998212290492660 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2730473518046994636871477981) ^ 546094703609398927374295596 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2730473518046994636871477981) ^ 60 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_3583746492436680460893814853 : Nat.Prime 3583746492436680460893814853 := by
  apply lucas_primality 3583746492436680460893814853 (2 : ZMod 3583746492436680460893814853)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (49789, 1), (268577163723201496951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (49789, 1), (268577163723201496951, 1)] : List FactorBlock).map factorBlockValue).prod) = 3583746492436680460893814853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_67
      · exact prime_ninetySevenCQ_49789
      · exact prime_ninetySevenCQ_268577163723201496951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3583746492436680460893814853) ^ 1791873246218340230446907426 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3583746492436680460893814853) ^ 53488753618457917326773356 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3583746492436680460893814853) ^ 71978679877818001182868 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3583746492436680460893814853) ^ 13343452 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_14334985969746721843575259403 : Nat.Prime 14334985969746721843575259403 := by
  apply lucas_primality 14334985969746721843575259403 (2 : ZMod 14334985969746721843575259403)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (43, 1), (2164751732066856213164491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (43, 1), (2164751732066856213164491, 1)] : List FactorBlock).map factorBlockValue).prod) = 14334985969746721843575259403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_7
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_43
      · exact prime_ninetySevenCQ_2164751732066856213164491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14334985969746721843575259403) ^ 7167492984873360921787629701 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14334985969746721843575259403) ^ 2047855138535245977653608486 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14334985969746721843575259403) ^ 1303180542704247440325023582 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14334985969746721843575259403) ^ 333371766738295856827331614 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14334985969746721843575259403) ^ 6622 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem prime_ninetySevenCQ_114679887757973774748602075239 : Nat.Prime 114679887757973774748602075239 := by
  apply lucas_primality 114679887757973774748602075239 (3 : ZMod 114679887757973774748602075239)
  · rw [← ninetySevenCQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1737574056938996587100031443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1737574056938996587100031443, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetySevenCQ_2
      · exact prime_ninetySevenCQ_3
      · exact prime_ninetySevenCQ_11
      · exact prime_ninetySevenCQ_1737574056938996587100031443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 114679887757973774748602075239) ^ 57339943878986887374301037619 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 114679887757973774748602075239) ^ 38226629252657924916200691746 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 114679887757973774748602075239) ^ 10425444341633979522600188658 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide
    · change (3 : ZMod 114679887757973774748602075239) ^ 66 ≠ 1
      rw [← ninetySevenCQFastPow_eq_pow]
      decide

private theorem phi_ninetySevenCQ_114679887757973774748602075200 : Nat.totient 114679887757973774748602075200 = 43986300562840462769998725120 := by
  rw [← show ((([(2, 6), (5, 2), (37, 1), (73, 1), (1277, 1), (136041979, 1), (152749168259, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_5, prime_ninetySevenCQ_37, prime_ninetySevenCQ_73, prime_ninetySevenCQ_1277, prime_ninetySevenCQ_136041979, prime_ninetySevenCQ_152749168259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075201 : Nat.totient 114679887757973774748602075201 = 114556443314746677036278498304 := by
  rw [← show ((([(929, 1), (123444443227097712323575969, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_929, prime_ninetySevenCQ_123444443227097712323575969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075202 : Nat.totient 114679887757973774748602075202 = 32765682216563935642457735760 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (2730473518046994636871477981, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_7, prime_ninetySevenCQ_2730473518046994636871477981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075203 : Nat.totient 114679887757973774748602075203 = 114415038125858766731764492800 := by
  rw [← show ((([(433, 1), (16806211171, 1), (15759032337051121, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_433, prime_ninetySevenCQ_16806211171, prime_ninetySevenCQ_15759032337051121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075204 : Nat.totient 114679887757973774748602075204 = 56078824196181226866168862080 := by
  rw [← show ((([(2, 2), (79, 1), (107, 1), (10181, 1), (81883, 1), (4068480283297979, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_79, prime_ninetySevenCQ_107, prime_ninetySevenCQ_10181, prime_ninetySevenCQ_81883, prime_ninetySevenCQ_4068480283297979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075205 : Nat.totient 114679887757973774748602075205 = 55314272266273650669085163520 := by
  rw [← show ((([(3, 2), (5, 1), (11, 1), (193, 1), (32989477, 1), (101666563, 1), (357907813, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_5, prime_ninetySevenCQ_11, prime_ninetySevenCQ_193, prime_ninetySevenCQ_32989477, prime_ninetySevenCQ_101666563, prime_ninetySevenCQ_357907813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075206 : Nat.totient 114679887757973774748602075206 = 52860115084531393057538620800 := by
  rw [← show ((([(2, 1), (13, 1), (787, 1), (29221, 1), (109037911, 1), (1759003008023, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_13, prime_ninetySevenCQ_787, prime_ninetySevenCQ_29221, prime_ninetySevenCQ_109037911, prime_ninetySevenCQ_1759003008023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075207 : Nat.totient 114679887757973774748602075207 = 112448331207072891406671519744 := by
  rw [← show ((([(53, 1), (1979, 1), (10289, 1), (106265533810697062849, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_53, prime_ninetySevenCQ_1979, prime_ninetySevenCQ_10289, prime_ninetySevenCQ_106265533810697062849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075208 : Nat.totient 114679887757973774748602075208 = 38226021523962555826056184832 := by
  rw [← show ((([(2, 3), (3, 1), (101939, 1), (164249, 1), (285386164317263897, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_101939, prime_ninetySevenCQ_164249, prime_ninetySevenCQ_285386164317263897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075209 : Nat.totient 114679887757973774748602075209 = 95066788905046039030661880000 := by
  rw [← show ((([(7, 1), (31, 1), (1637, 1), (74551, 1), (4330373662105114571, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_7, prime_ninetySevenCQ_31, prime_ninetySevenCQ_1637, prime_ninetySevenCQ_74551, prime_ninetySevenCQ_4330373662105114571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075210 : Nat.totient 114679887757973774748602075210 = 43799519294029032760306080000 := by
  rw [← show ((([(2, 1), (5, 1), (23, 1), (563, 1), (661883, 1), (27457501, 1), (48731389363, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_5, prime_ninetySevenCQ_23, prime_ninetySevenCQ_563, prime_ninetySevenCQ_661883, prime_ninetySevenCQ_27457501, prime_ninetySevenCQ_48731389363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075211 : Nat.totient 114679887757973774748602075211 = 76133370365466762580810411680 := by
  rw [← show ((([(3, 1), (239, 1), (2629987891, 1), (60815510215005613, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_239, prime_ninetySevenCQ_2629987891, prime_ninetySevenCQ_60815510215005613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075212 : Nat.totient 114679887757973774748602075212 = 57317288786236138407720500880 := by
  rw [← show ((([(2, 2), (2531, 1), (1513146007, 1), (7486076943793559, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_2531, prime_ninetySevenCQ_1513146007, prime_ninetySevenCQ_7486076943793559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075213 : Nat.totient 114679887757973774748602075213 = 114679887357424071932093476320 := by
  rw [← show ((([(286306261, 1), (400549702816222292633, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_286306261, prime_ninetySevenCQ_400549702816222292633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075214 : Nat.totient 114679887757973774748602075214 = 38226629252656708781756879040 := by
  rw [← show ((([(2, 1), (3, 2), (38897677166321, 1), (163791396802463, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_38897677166321, prime_ninetySevenCQ_163791396802463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075215 : Nat.totient 114679887757973774748602075215 = 86318117340451352952007716864 := by
  rw [← show ((([(5, 1), (17, 1), (2969, 1), (9242983, 1), (49163860943746877, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_5, prime_ninetySevenCQ_17, prime_ninetySevenCQ_2969, prime_ninetySevenCQ_9242983, prime_ninetySevenCQ_49163860943746877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075216 : Nat.totient 114679887757973774748602075216 = 43641394918467821257396118400 := by
  rw [← show ((([(2, 4), (7, 1), (11, 1), (43, 1), (2164751732066856213164491, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_7, prime_ninetySevenCQ_11, prime_ninetySevenCQ_43, prime_ninetySevenCQ_2164751732066856213164491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075217 : Nat.totient 114679887757973774748602075217 = 75961377995633650055187970560 := by
  rw [← show ((([(3, 1), (173, 1), (2111, 1), (6823, 1), (27017, 1), (567831098595143, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_173, prime_ninetySevenCQ_2111, prime_ninetySevenCQ_6823, prime_ninetySevenCQ_27017, prime_ninetySevenCQ_567831098595143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075218 : Nat.totient 114679887757973774748602075218 = 53556952770232814244751290000 := by
  rw [← show ((([(2, 1), (19, 1), (71, 1), (150782672351, 1), (281899222298891, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_19, prime_ninetySevenCQ_71, prime_ninetySevenCQ_150782672351, prime_ninetySevenCQ_281899222298891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075219 : Nat.totient 114679887757973774748602075219 = 103958975199039534803720074752 := by
  rw [← show ((([(13, 1), (109, 1), (113, 2), (6338120941943284525403, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_13, prime_ninetySevenCQ_109, prime_ninetySevenCQ_113, prime_ninetySevenCQ_6338120941943284525403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075220 : Nat.totient 114679887757973774748602075220 = 29945082799112169955673871360 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (61, 1), (223, 1), (140508083704542839506729, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_5, prime_ninetySevenCQ_61, prime_ninetySevenCQ_223, prime_ninetySevenCQ_140508083704542839506729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075221 : Nat.totient 114679887757973774748602075221 = 114494020476124232553160024320 := by
  rw [← show ((([(617, 1), (313768361, 1), (592369850029953733, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_617, prime_ninetySevenCQ_313768361, prime_ninetySevenCQ_592369850029953733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075222 : Nat.totient 114679887757973774748602075222 = 57224703355298923881853569024 := by
  rw [← show ((([(2, 1), (853, 1), (1217, 1), (59707, 1), (925107929942445773, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_853, prime_ninetySevenCQ_1217, prime_ninetySevenCQ_59707, prime_ninetySevenCQ_925107929942445773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075223 : Nat.totient 114679887757973774748602075223 = 63128836775671543869679185408 := by
  rw [← show ((([(3, 3), (7, 2), (29, 1), (443, 1), (4863559817, 1), (1387303331699, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_7, prime_ninetySevenCQ_29, prime_ninetySevenCQ_443, prime_ninetySevenCQ_4863559817, prime_ninetySevenCQ_1387303331699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075224 : Nat.totient 114679887757973774748602075224 = 57339943878986887374301037608 := by
  rw [← show ((([(2, 3), (14334985969746721843575259403, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_14334985969746721843575259403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075225 : Nat.totient 114679887757973774748602075225 = 91743862087589204362244806080 := by
  rw [← show ((([(5, 2), (1906613, 1), (2405939490771829936093, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_5, prime_ninetySevenCQ_1906613, prime_ninetySevenCQ_2405939490771829936093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075226 : Nat.totient 114679887757973774748602075226 = 37847590865096224775742320000 := by
  rw [← show ((([(2, 1), (3, 1), (101, 1), (67961, 1), (2784549063058874689211, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_101, prime_ninetySevenCQ_67961, prime_ninetySevenCQ_2784549063058874689211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075227 : Nat.totient 114679887757973774748602075227 = 104252570953286482659206246400 := by
  rw [← show ((([(11, 1), (94441, 1), (135649, 1), (813799465994653673, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_11, prime_ninetySevenCQ_94441, prime_ninetySevenCQ_135649, prime_ninetySevenCQ_813799465994653673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075228 : Nat.totient 114679887757973774748602075228 = 57339585422690860078447741184 := by
  rw [← show ((([(2, 2), (159977, 1), (1903552247, 1), (94146660164153, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_159977, prime_ninetySevenCQ_1903552247, prime_ninetySevenCQ_94146660164153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075229 : Nat.totient 114679887757973774748602075229 = 76022151730247233364396359040 := by
  rw [← show ((([(3, 1), (179, 1), (19037, 1), (11217974891194807910441, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_179, prime_ninetySevenCQ_19037, prime_ninetySevenCQ_11217974891194807910441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075230 : Nat.totient 114679887757973774748602075230 = 39197977101311711897727152640 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (367, 1), (2861, 1), (173124323, 1), (9012540078589, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_5, prime_ninetySevenCQ_7, prime_ninetySevenCQ_367, prime_ninetySevenCQ_2861, prime_ninetySevenCQ_173124323, prime_ninetySevenCQ_9012540078589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075231 : Nat.totient 114679887757973774748602075231 = 114256714740416675948791735200 := by
  rw [← show ((([(271, 1), (423173017557098799810339761, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_271, prime_ninetySevenCQ_423173017557098799810339761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075232 : Nat.totient 114679887757973774748602075232 = 33210465233078378207739949056 := by
  rw [← show ((([(2, 5), (3, 2), (13, 1), (17, 1), (1801783053009894651027559, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_13, prime_ninetySevenCQ_17, prime_ninetySevenCQ_1801783053009894651027559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075233 : Nat.totient 114679887757973774748602075233 = 109693782049633878187132898560 := by
  rw [← show ((([(23, 1), (6698291, 1), (15118673, 1), (49235883827597, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_23, prime_ninetySevenCQ_6698291, prime_ninetySevenCQ_15118673, prime_ninetySevenCQ_49235883827597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075234 : Nat.totient 114679887757973774748602075234 = 55903441329704328844818385728 := by
  rw [← show ((([(2, 1), (47, 1), (607, 1), (719, 1), (1213, 1), (2304522874688847259, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_47, prime_ninetySevenCQ_607, prime_ninetySevenCQ_719, prime_ninetySevenCQ_1213, prime_ninetySevenCQ_2304522874688847259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075235 : Nat.totient 114679887757973774748602075235 = 60054998062509616330763141760 := by
  rw [← show ((([(3, 1), (5, 1), (83, 1), (163, 1), (565106500889318130182581, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_5, prime_ninetySevenCQ_83, prime_ninetySevenCQ_163, prime_ninetySevenCQ_565106500889318130182581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075236 : Nat.totient 114679887757973774748602075236 = 56748765610742405541080583168 := by
  rw [← show ((([(2, 2), (97, 1), (1266487, 1), (3270900859, 1), (71348922109, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_97, prime_ninetySevenCQ_1266487, prime_ninetySevenCQ_3270900859, prime_ninetySevenCQ_71348922109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075237 : Nat.totient 114679887757973774748602075237 = 88390407566047853346666854400 := by
  rw [← show ((([(7, 1), (19, 1), (37, 1), (41, 1), (18199, 1), (59621, 1), (523845546942023, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_7, prime_ninetySevenCQ_19, prime_ninetySevenCQ_37, prime_ninetySevenCQ_41, prime_ninetySevenCQ_18199, prime_ninetySevenCQ_59621, prime_ninetySevenCQ_523845546942023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075238 : Nat.totient 114679887757973774748602075238 = 34751481138779931742000628840 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (1737574056938996587100031443, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_11, prime_ninetySevenCQ_1737574056938996587100031443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075239 : Nat.totient 114679887757973774748602075239 = 114679887757973774748602075238 := by
  rw [← show ((([(114679887757973774748602075239, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_114679887757973774748602075239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075240 : Nat.totient 114679887757973774748602075240 = 44392214615989848289781448000 := by
  rw [← show ((([(2, 3), (5, 1), (31, 1), (92483780449978850603711351, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_5, prime_ninetySevenCQ_31, prime_ninetySevenCQ_92483780449978850603711351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075241 : Nat.totient 114679887757973774748602075241 = 75214362448218941223238600704 := by
  rw [← show ((([(3, 2), (89, 1), (199, 1), (463150607, 1), (1553386151736737, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_89, prime_ninetySevenCQ_199, prime_ninetySevenCQ_463150607, prime_ninetySevenCQ_1553386151736737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075242 : Nat.totient 114679887757973774748602075242 = 56955112033969748775560886160 := by
  rw [← show ((([(2, 1), (149, 1), (8250619691, 1), (46642779879163619, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_149, prime_ninetySevenCQ_8250619691, prime_ninetySevenCQ_46642779879163619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075243 : Nat.totient 114679887757973774748602075243 = 114679374513368899305980539680 := by
  rw [← show ((([(223441, 1), (513244604875442621312123, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_223441, prime_ninetySevenCQ_513244604875442621312123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075244 : Nat.totient 114679887757973774748602075244 = 32765678965886385469681444608 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (10079647, 1), (135444897923855599153, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_7, prime_ninetySevenCQ_10079647, prime_ninetySevenCQ_135444897923855599153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075245 : Nat.totient 114679887757973774748602075245 = 84686162184670515491552784384 := by
  rw [← show ((([(5, 1), (13, 1), (165569, 1), (6683519, 1), (1594372113927443, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_5, prime_ninetySevenCQ_13, prime_ninetySevenCQ_165569, prime_ninetySevenCQ_6683519, prime_ninetySevenCQ_1594372113927443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075246 : Nat.totient 114679887757973774748602075246 = 57338704873306579094360320608 := by
  rw [← show ((([(2, 1), (46279, 1), (1239005680308279940670737, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_46279, prime_ninetySevenCQ_1239005680308279940670737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075247 : Nat.totient 114679887757973774748602075247 = 75851264342025214411244440320 := by
  rw [← show ((([(3, 1), (127, 1), (41416074017, 1), (7267639144310011, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_127, prime_ninetySevenCQ_41416074017, prime_ninetySevenCQ_7267639144310011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075248 : Nat.totient 114679887757973774748602075248 = 56959752450281568274725888000 := by
  rw [← show ((([(2, 4), (151, 1), (124721, 1), (380584191591041053793, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_151, prime_ninetySevenCQ_124721, prime_ninetySevenCQ_380584191591041053793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075249 : Nat.totient 114679887757973774748602075249 = 98121829097687717137583784960 := by
  rw [← show ((([(11, 1), (17, 1), (2255991565649, 1), (271836757370323, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_11, prime_ninetySevenCQ_17, prime_ninetySevenCQ_2255991565649, prime_ninetySevenCQ_271836757370323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075250 : Nat.totient 114679887757973774748602075250 = 30581125631756560035658382400 := by
  rw [← show ((([(2, 1), (3, 3), (5, 3), (172027, 1), (98761316544387218069, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_5, prime_ninetySevenCQ_172027, prime_ninetySevenCQ_98761316544387218069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075251 : Nat.totient 114679887757973774748602075251 = 98276474717320984067985716736 := by
  rw [← show ((([(7, 1), (5077, 1), (86929, 1), (1226387, 1), (30268425737483, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_7, prime_ninetySevenCQ_5077, prime_ninetySevenCQ_86929, prime_ninetySevenCQ_1226387, prime_ninetySevenCQ_30268425737483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075252 : Nat.totient 114679887757973774748602075252 = 54424346806722787098455623680 := by
  rw [← show ((([(2, 2), (29, 1), (59, 1), (9168721, 1), (70906357, 1), (25774089239, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_29, prime_ninetySevenCQ_59, prime_ninetySevenCQ_9168721, prime_ninetySevenCQ_70906357, prime_ninetySevenCQ_25774089239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075253 : Nat.totient 114679887757973774748602075253 = 76148663841494982957213750000 := by
  rw [← show ((([(3, 1), (251, 1), (9042498151, 1), (16842395227140851, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_251, prime_ninetySevenCQ_9042498151, prime_ninetySevenCQ_16842395227140851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075254 : Nat.totient 114679887757973774748602075254 = 57207409139424855038254506720 := by
  rw [← show ((([(2, 1), (467, 1), (5939, 1), (488981, 1), (42280009219535959, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_467, prime_ninetySevenCQ_5939, prime_ninetySevenCQ_488981, prime_ninetySevenCQ_42280009219535959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075255 : Nat.totient 114679887757973774748602075255 = 91742750520492020784587517600 := by
  rw [← show ((([(5, 1), (79111, 1), (289921471749753573456541, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_5, prime_ninetySevenCQ_79111, prime_ninetySevenCQ_289921471749753573456541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075256 : Nat.totient 114679887757973774748602075256 = 34629981816198139203750952320 := by
  rw [← show ((([(2, 3), (3, 1), (19, 1), (23, 1), (3407, 1), (3209389644407053061791, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_19, prime_ninetySevenCQ_23, prime_ninetySevenCQ_3407, prime_ninetySevenCQ_3209389644407053061791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075257 : Nat.totient 114679887757973774748602075257 = 113999525930889371875923834000 := by
  rw [← show ((([(191, 1), (1427, 1), (420755613533953539071101, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_191, prime_ninetySevenCQ_1427, prime_ninetySevenCQ_420755613533953539071101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075258 : Nat.totient 114679887757973774748602075258 = 45367867684369447230988378368 := by
  rw [← show ((([(2, 1), (7, 1), (13, 1), (437647993463, 1), (1439762738107313, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_7, prime_ninetySevenCQ_13, prime_ninetySevenCQ_437647993463, prime_ninetySevenCQ_1439762738107313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075259 : Nat.totient 114679887757973774748602075259 = 74675191052899897802548738560 := by
  rw [← show ((([(3, 2), (43, 1), (881681, 1), (336097136405264092697, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_43, prime_ninetySevenCQ_881681, prime_ninetySevenCQ_336097136405264092697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075260 : Nat.totient 114679887757973774748602075260 = 40914951378385677123297361920 := by
  rw [← show ((([(2, 2), (5, 1), (11, 1), (53, 1), (406292139733, 1), (24207519390017, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_5, prime_ninetySevenCQ_11, prime_ninetySevenCQ_53, prime_ninetySevenCQ_406292139733, prime_ninetySevenCQ_24207519390017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075261 : Nat.totient 114679887757973774748602075261 = 113554294211493837231553981440 := by
  rw [← show ((([(103, 1), (12917, 1), (33457, 1), (10896461, 1), (236437255643, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_103, prime_ninetySevenCQ_12917, prime_ninetySevenCQ_33457, prime_ninetySevenCQ_10896461, prime_ninetySevenCQ_236437255643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075262 : Nat.totient 114679887757973774748602075262 = 37947623382080936452857427200 := by
  rw [← show ((([(2, 1), (3, 1), (139, 1), (15901, 1), (23609, 1), (366285037865617027, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_139, prime_ninetySevenCQ_15901, prime_ninetySevenCQ_23609, prime_ninetySevenCQ_366285037865617027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075263 : Nat.totient 114679887757973774748602075263 = 114679827425782550555600167296 := by
  rw [← show ((([(1901117, 1), (11706188987, 1), (5153032513297, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_1901117, prime_ninetySevenCQ_11706188987, prime_ninetySevenCQ_5153032513297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075264 : Nat.totient 114679887757973774748602075264 = 56482989351151993893739238400 := by
  rw [← show ((([(2, 7), (67, 1), (49789, 1), (268577163723201496951, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_67, prime_ninetySevenCQ_49789, prime_ninetySevenCQ_268577163723201496951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075265 : Nat.totient 114679887757973774748602075265 = 52425081769034365574031125184 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (5361827, 1), (203697248571950914259, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_5, prime_ninetySevenCQ_7, prime_ninetySevenCQ_5361827, prime_ninetySevenCQ_203697248571950914259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075266 : Nat.totient 114679887757973774748602075266 = 53943408610476753773999609856 := by
  rw [← show ((([(2, 1), (17, 1), (2287, 1), (530805823, 1), (2778475035927649, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_17, prime_ninetySevenCQ_2287, prime_ninetySevenCQ_530805823, prime_ninetySevenCQ_2778475035927649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075267 : Nat.totient 114679887757973774748602075267 = 114679770542425338614862065920 := by
  rw [← show ((([(978473, 1), (9083804699, 1), (12902403650321, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_978473, prime_ninetySevenCQ_9083804699, prime_ninetySevenCQ_12902403650321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075268 : Nat.totient 114679887757973774748602075268 = 38222354472467950887302304000 := by
  rw [← show ((([(2, 2), (3, 2), (12107, 1), (34213, 1), (239890093, 1), (32058614251, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_12107, prime_ninetySevenCQ_34213, prime_ninetySevenCQ_239890093, prime_ninetySevenCQ_32058614251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075269 : Nat.totient 114679887757973774748602075269 = 114519524203571940624687290496 := by
  rw [← show ((([(739, 1), (23993, 1), (280843, 1), (23030038459851629, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_739, prime_ninetySevenCQ_23993, prime_ninetySevenCQ_280843, prime_ninetySevenCQ_23030038459851629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075270 : Nat.totient 114679887757973774748602075270 = 45871955099235184915225112544 := by
  rw [← show ((([(2, 1), (5, 1), (11600451613, 1), (988581234453477779, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_5, prime_ninetySevenCQ_11600451613, prime_ninetySevenCQ_988581234453477779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075271 : Nat.totient 114679887757973774748602075271 = 62087013448687453637072764800 := by
  rw [← show ((([(3, 1), (11, 1), (13, 1), (31, 1), (250763793263, 1), (34387724799283, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_11, prime_ninetySevenCQ_13, prime_ninetySevenCQ_31, prime_ninetySevenCQ_250763793263, prime_ninetySevenCQ_34387724799283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075272 : Nat.totient 114679887757973774748602075272 = 49148523324845903463686603520 := by
  rw [← show ((([(2, 3), (7, 2), (292550734076463711093372641, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_7, prime_ninetySevenCQ_292550734076463711093372641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075273 : Nat.totient 114679887757973774748602075273 = 113005445549252851931974170624 := by
  rw [← show ((([(73, 1), (1093, 1), (58845392273, 1), (24424842666109, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_73, prime_ninetySevenCQ_1093, prime_ninetySevenCQ_58845392273, prime_ninetySevenCQ_24424842666109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075274 : Nat.totient 114679887757973774748602075274 = 37193458426203933344249012160 := by
  rw [← show ((([(2, 1), (3, 1), (37, 1), (1990607, 1), (259506809220435701381, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_37, prime_ninetySevenCQ_1990607, prime_ninetySevenCQ_259506809220435701381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075275 : Nat.totient 114679887757973774748602075275 = 86788028003254164511140015360 := by
  rw [← show ((([(5, 2), (19, 1), (683, 1), (490680539, 1), (720400676940937, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_5, prime_ninetySevenCQ_19, prime_ninetySevenCQ_683, prime_ninetySevenCQ_490680539, prime_ninetySevenCQ_720400676940937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075276 : Nat.totient 114679887757973774748602075276 = 57285352384712922009601689600 := by
  rw [← show ((([(2, 2), (1051, 1), (1968257, 1), (11741759, 1), (1180346685863, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_1051, prime_ninetySevenCQ_1968257, prime_ninetySevenCQ_11741759, prime_ninetySevenCQ_1180346685863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075277 : Nat.totient 114679887757973774748602075277 = 76229431428667611476422656000 := by
  rw [← show ((([(3, 4), (463, 1), (1601, 1), (6899, 1), (276849518456303041, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_463, prime_ninetySevenCQ_1601, prime_ninetySevenCQ_6899, prime_ninetySevenCQ_276849518456303041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075278 : Nat.totient 114679887757973774748602075278 = 55941408662426231584683939120 := by
  rw [← show ((([(2, 1), (41, 1), (1398535216560655789617098479, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_41, prime_ninetySevenCQ_1398535216560655789617098479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075279 : Nat.totient 114679887757973774748602075279 = 94006798475362456786038562560 := by
  rw [← show ((([(7, 1), (23, 1), (5711, 1), (124723768077485613737249, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_7, prime_ninetySevenCQ_23, prime_ninetySevenCQ_5711, prime_ninetySevenCQ_124723768077485613737249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075280 : Nat.totient 114679887757973774748602075280 = 30581248264218205858068470784 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (554633, 1), (861529814594919634159, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_5, prime_ninetySevenCQ_554633, prime_ninetySevenCQ_861529814594919634159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075281 : Nat.totient 114679887757973774748602075281 = 106245790633483488648524021760 := by
  rw [← show ((([(29, 1), (47, 1), (61, 1), (307, 1), (4956924737, 1), (906381156413, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_29, prime_ninetySevenCQ_47, prime_ninetySevenCQ_61, prime_ninetySevenCQ_307, prime_ninetySevenCQ_4956924737, prime_ninetySevenCQ_906381156413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075282 : Nat.totient 114679887757973774748602075282 = 52127221708144534773673910520 := by
  rw [← show ((([(2, 1), (11, 2), (2073913890343, 1), (228497352719047, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_11, prime_ninetySevenCQ_2073913890343, prime_ninetySevenCQ_228497352719047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075283 : Nat.totient 114679887757973774748602075283 = 71045172460457260471896482304 := by
  rw [← show ((([(3, 1), (17, 2), (79, 1), (444275901467, 1), (3768671762893, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_17, prime_ninetySevenCQ_79, prime_ninetySevenCQ_444275901467, prime_ninetySevenCQ_3768671762893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075284 : Nat.totient 114679887757973774748602075284 = 52928469921877917757443239040 := by
  rw [← show ((([(2, 2), (13, 1), (133669, 1), (169063, 1), (97589848846413811, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_13, prime_ninetySevenCQ_133669, prime_ninetySevenCQ_169063, prime_ninetySevenCQ_97589848846413811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075285 : Nat.totient 114679887757973774748602075285 = 91738459317530681671628376720 := by
  rw [← show ((([(5, 1), (16831, 1), (1362722212084531813304047, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_5, prime_ninetySevenCQ_16831, prime_ninetySevenCQ_1362722212084531813304047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075286 : Nat.totient 114679887757973774748602075286 = 32765682216563935642457735760 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (910157839348998212290492661, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_7, prime_ninetySevenCQ_910157839348998212290492661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075287 : Nat.totient 114679887757973774748602075287 = 114624961775167857158402214240 := by
  rw [← show ((([(2141, 1), (84143, 1), (636579428229403127149, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2141, prime_ninetySevenCQ_84143, prime_ninetySevenCQ_636579428229403127149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075288 : Nat.totient 114679887757973774748602075288 = 57250489988380043556244403200 := by
  rw [← show ((([(2, 3), (641, 1), (22363472651710954514157971, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_641, prime_ninetySevenCQ_22363472651710954514157971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075289 : Nat.totient 114679887757973774748602075289 = 75208575751942501913721528320 := by
  rw [← show ((([(3, 1), (71, 1), (449, 1), (7254044009, 1), (165303149698733, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_71, prime_ninetySevenCQ_449, prime_ninetySevenCQ_7254044009, prime_ninetySevenCQ_165303149698733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075290 : Nat.totient 114679887757973774748602075290 = 45871955102165849911838811136 := by
  rw [← show ((([(2, 1), (5, 1), (44811718433, 1), (255914952088786313, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_5, prime_ninetySevenCQ_44811718433, prime_ninetySevenCQ_255914952088786313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075291 : Nat.totient 114679887757973774748602075291 = 114679116598558815708754513800 := by
  rw [← show ((([(148711, 1), (771159414959039847412781, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_148711, prime_ninetySevenCQ_771159414959039847412781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075292 : Nat.totient 114679887757973774748602075292 = 38058861293826608344860241920 := by
  rw [← show ((([(2, 2), (3, 1), (229, 1), (50893, 1), (423461, 1), (41300317, 1), (46886269, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_229, prime_ninetySevenCQ_50893, prime_ninetySevenCQ_423461, prime_ninetySevenCQ_41300317, prime_ninetySevenCQ_46886269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075293 : Nat.totient 114679887757973774748602075293 = 89342070842959384910012367360 := by
  rw [← show ((([(7, 1), (11, 1), (4733, 1), (353278829, 1), (890722488704537, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_7, prime_ninetySevenCQ_11, prime_ninetySevenCQ_4733, prime_ninetySevenCQ_353278829, prime_ninetySevenCQ_890722488704537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075294 : Nat.totient 114679887757973774748602075294 = 54128735184509067684299906880 := by
  rw [← show ((([(2, 1), (19, 1), (281, 1), (10739828409624815016726173, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_19, prime_ninetySevenCQ_281, prime_ninetySevenCQ_10739828409624815016726173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075295 : Nat.totient 114679887757973774748602075295 = 61162606791863423810239013568 := by
  rw [← show ((([(3, 2), (5, 1), (4936745767, 1), (516218997383341453, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_5, prime_ninetySevenCQ_4936745767, prime_ninetySevenCQ_516218997383341453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075296 : Nat.totient 114679887757973774748602075296 = 57339943878986887374301037632 := by
  rw [← show ((([(2, 5), (3583746492436680460893814853, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3583746492436680460893814853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075297 : Nat.totient 114679887757973774748602075297 = 105711952312055889212175460800 := by
  rw [← show ((([(13, 1), (811, 1), (6659, 1), (1633480813824266132581, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_13, prime_ninetySevenCQ_811, prime_ninetySevenCQ_6659, prime_ninetySevenCQ_1633480813824266132581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075298 : Nat.totient 114679887757973774748602075298 = 38217380128715834927108934000 := by
  rw [← show ((([(2, 1), (3, 1), (4133, 1), (4624561971044994545874751, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_3, prime_ninetySevenCQ_4133, prime_ninetySevenCQ_4624561971044994545874751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075299 : Nat.totient 114679887757973774748602075299 = 114542918161910595312591329856 := by
  rw [← show ((([(1097, 1), (3533, 1), (29589456915787305250999, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_1097, prime_ninetySevenCQ_3533, prime_ninetySevenCQ_29589456915787305250999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075300 : Nat.totient 114679887757973774748602075300 = 37001821910243511786877900800 := by
  rw [← show ((([(2, 2), (5, 2), (7, 1), (17, 1), (8971, 1), (1074235353674386606597, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_2, prime_ninetySevenCQ_5, prime_ninetySevenCQ_7, prime_ninetySevenCQ_17, prime_ninetySevenCQ_8971, prime_ninetySevenCQ_1074235353674386606597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetySevenCQ_114679887757973774748602075301 : Nat.totient 114679887757973774748602075301 = 75868018835232838918742064000 := by
  rw [← show ((([(3, 1), (131, 1), (48809, 1), (1045151, 1), (5720259861641323, 1)] : List FactorBlock).map factorBlockValue).prod) = 114679887757973774748602075301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetySevenCQ_3, prime_ninetySevenCQ_131, prime_ninetySevenCQ_48809, prime_ninetySevenCQ_1045151, prime_ninetySevenCQ_5720259861641323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NinetySevenCQ : certifiedKill 1 114679887757973774748602075199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_ninetySevenCQ_114679887757973774748602075200, phi_ninetySevenCQ_114679887757973774748602075201, phi_ninetySevenCQ_114679887757973774748602075202,
    phi_ninetySevenCQ_114679887757973774748602075203, phi_ninetySevenCQ_114679887757973774748602075204, phi_ninetySevenCQ_114679887757973774748602075205,
    phi_ninetySevenCQ_114679887757973774748602075206, phi_ninetySevenCQ_114679887757973774748602075207, phi_ninetySevenCQ_114679887757973774748602075208,
    phi_ninetySevenCQ_114679887757973774748602075209, phi_ninetySevenCQ_114679887757973774748602075210, phi_ninetySevenCQ_114679887757973774748602075211,
    phi_ninetySevenCQ_114679887757973774748602075212, phi_ninetySevenCQ_114679887757973774748602075213, phi_ninetySevenCQ_114679887757973774748602075214,
    phi_ninetySevenCQ_114679887757973774748602075215, phi_ninetySevenCQ_114679887757973774748602075216, phi_ninetySevenCQ_114679887757973774748602075217,
    phi_ninetySevenCQ_114679887757973774748602075218, phi_ninetySevenCQ_114679887757973774748602075219, phi_ninetySevenCQ_114679887757973774748602075220,
    phi_ninetySevenCQ_114679887757973774748602075221, phi_ninetySevenCQ_114679887757973774748602075222, phi_ninetySevenCQ_114679887757973774748602075223,
    phi_ninetySevenCQ_114679887757973774748602075224, phi_ninetySevenCQ_114679887757973774748602075225, phi_ninetySevenCQ_114679887757973774748602075226,
    phi_ninetySevenCQ_114679887757973774748602075227, phi_ninetySevenCQ_114679887757973774748602075228, phi_ninetySevenCQ_114679887757973774748602075229,
    phi_ninetySevenCQ_114679887757973774748602075230, phi_ninetySevenCQ_114679887757973774748602075231, phi_ninetySevenCQ_114679887757973774748602075232,
    phi_ninetySevenCQ_114679887757973774748602075233, phi_ninetySevenCQ_114679887757973774748602075234, phi_ninetySevenCQ_114679887757973774748602075235,
    phi_ninetySevenCQ_114679887757973774748602075236, phi_ninetySevenCQ_114679887757973774748602075237, phi_ninetySevenCQ_114679887757973774748602075238,
    phi_ninetySevenCQ_114679887757973774748602075239, phi_ninetySevenCQ_114679887757973774748602075240, phi_ninetySevenCQ_114679887757973774748602075241,
    phi_ninetySevenCQ_114679887757973774748602075242, phi_ninetySevenCQ_114679887757973774748602075243, phi_ninetySevenCQ_114679887757973774748602075244,
    phi_ninetySevenCQ_114679887757973774748602075245, phi_ninetySevenCQ_114679887757973774748602075246, phi_ninetySevenCQ_114679887757973774748602075247,
    phi_ninetySevenCQ_114679887757973774748602075248, phi_ninetySevenCQ_114679887757973774748602075249, phi_ninetySevenCQ_114679887757973774748602075250,
    phi_ninetySevenCQ_114679887757973774748602075251, phi_ninetySevenCQ_114679887757973774748602075252, phi_ninetySevenCQ_114679887757973774748602075253,
    phi_ninetySevenCQ_114679887757973774748602075254, phi_ninetySevenCQ_114679887757973774748602075255, phi_ninetySevenCQ_114679887757973774748602075256,
    phi_ninetySevenCQ_114679887757973774748602075257, phi_ninetySevenCQ_114679887757973774748602075258, phi_ninetySevenCQ_114679887757973774748602075259,
    phi_ninetySevenCQ_114679887757973774748602075260, phi_ninetySevenCQ_114679887757973774748602075261, phi_ninetySevenCQ_114679887757973774748602075262,
    phi_ninetySevenCQ_114679887757973774748602075263, phi_ninetySevenCQ_114679887757973774748602075264, phi_ninetySevenCQ_114679887757973774748602075265,
    phi_ninetySevenCQ_114679887757973774748602075266, phi_ninetySevenCQ_114679887757973774748602075267, phi_ninetySevenCQ_114679887757973774748602075268,
    phi_ninetySevenCQ_114679887757973774748602075269, phi_ninetySevenCQ_114679887757973774748602075270, phi_ninetySevenCQ_114679887757973774748602075271,
    phi_ninetySevenCQ_114679887757973774748602075272, phi_ninetySevenCQ_114679887757973774748602075273, phi_ninetySevenCQ_114679887757973774748602075274,
    phi_ninetySevenCQ_114679887757973774748602075275, phi_ninetySevenCQ_114679887757973774748602075276, phi_ninetySevenCQ_114679887757973774748602075277,
    phi_ninetySevenCQ_114679887757973774748602075278, phi_ninetySevenCQ_114679887757973774748602075279, phi_ninetySevenCQ_114679887757973774748602075280,
    phi_ninetySevenCQ_114679887757973774748602075281, phi_ninetySevenCQ_114679887757973774748602075282, phi_ninetySevenCQ_114679887757973774748602075283,
    phi_ninetySevenCQ_114679887757973774748602075284, phi_ninetySevenCQ_114679887757973774748602075285, phi_ninetySevenCQ_114679887757973774748602075286,
    phi_ninetySevenCQ_114679887757973774748602075287, phi_ninetySevenCQ_114679887757973774748602075288, phi_ninetySevenCQ_114679887757973774748602075289,
    phi_ninetySevenCQ_114679887757973774748602075290, phi_ninetySevenCQ_114679887757973774748602075291, phi_ninetySevenCQ_114679887757973774748602075292,
    phi_ninetySevenCQ_114679887757973774748602075293, phi_ninetySevenCQ_114679887757973774748602075294, phi_ninetySevenCQ_114679887757973774748602075295,
    phi_ninetySevenCQ_114679887757973774748602075296, phi_ninetySevenCQ_114679887757973774748602075297, phi_ninetySevenCQ_114679887757973774748602075298,
    phi_ninetySevenCQ_114679887757973774748602075299, phi_ninetySevenCQ_114679887757973774748602075300, phi_ninetySevenCQ_114679887757973774748602075301
    ]

end TotientTailPeriodKiller
end Erdos249257
