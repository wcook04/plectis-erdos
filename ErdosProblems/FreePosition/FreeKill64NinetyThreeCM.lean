import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def ninetyThreeCMFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem ninetyThreeCMFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : ninetyThreeCMFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [ninetyThreeCMFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [ninetyThreeCMFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then ninetyThreeCMFastPow a n * ninetyThreeCMFastPow a n * a else ninetyThreeCMFastPow a n * ninetyThreeCMFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_ninetyThreeCM_2 : Nat.Prime 2 := by norm_num

private theorem prime_ninetyThreeCM_3 : Nat.Prime 3 := by norm_num

private theorem prime_ninetyThreeCM_5 : Nat.Prime 5 := by norm_num

private theorem prime_ninetyThreeCM_7 : Nat.Prime 7 := by norm_num

private theorem prime_ninetyThreeCM_11 : Nat.Prime 11 := by norm_num

private theorem prime_ninetyThreeCM_13 : Nat.Prime 13 := by norm_num

private theorem prime_ninetyThreeCM_17 : Nat.Prime 17 := by norm_num

private theorem prime_ninetyThreeCM_19 : Nat.Prime 19 := by norm_num

private theorem prime_ninetyThreeCM_23 : Nat.Prime 23 := by norm_num

private theorem prime_ninetyThreeCM_29 : Nat.Prime 29 := by norm_num

private theorem prime_ninetyThreeCM_31 : Nat.Prime 31 := by norm_num

private theorem prime_ninetyThreeCM_37 : Nat.Prime 37 := by norm_num

private theorem prime_ninetyThreeCM_41 : Nat.Prime 41 := by norm_num

private theorem prime_ninetyThreeCM_43 : Nat.Prime 43 := by norm_num

private theorem prime_ninetyThreeCM_47 : Nat.Prime 47 := by norm_num

private theorem prime_ninetyThreeCM_53 : Nat.Prime 53 := by norm_num

private theorem prime_ninetyThreeCM_59 : Nat.Prime 59 := by norm_num

private theorem prime_ninetyThreeCM_61 : Nat.Prime 61 := by norm_num

private theorem prime_ninetyThreeCM_67 : Nat.Prime 67 := by norm_num

private theorem prime_ninetyThreeCM_71 : Nat.Prime 71 := by norm_num

private theorem prime_ninetyThreeCM_73 : Nat.Prime 73 := by norm_num

private theorem prime_ninetyThreeCM_79 : Nat.Prime 79 := by norm_num

private theorem prime_ninetyThreeCM_83 : Nat.Prime 83 := by norm_num

private theorem prime_ninetyThreeCM_89 : Nat.Prime 89 := by norm_num

private theorem prime_ninetyThreeCM_97 : Nat.Prime 97 := by norm_num

private theorem prime_ninetyThreeCM_101 : Nat.Prime 101 := by norm_num

private theorem prime_ninetyThreeCM_103 : Nat.Prime 103 := by norm_num

private theorem prime_ninetyThreeCM_107 : Nat.Prime 107 := by norm_num

private theorem prime_ninetyThreeCM_109 : Nat.Prime 109 := by norm_num

private theorem prime_ninetyThreeCM_113 : Nat.Prime 113 := by norm_num

private theorem prime_ninetyThreeCM_127 : Nat.Prime 127 := by norm_num

private theorem prime_ninetyThreeCM_131 : Nat.Prime 131 := by norm_num

private theorem prime_ninetyThreeCM_137 : Nat.Prime 137 := by norm_num

private theorem prime_ninetyThreeCM_139 : Nat.Prime 139 := by norm_num

private theorem prime_ninetyThreeCM_149 : Nat.Prime 149 := by norm_num

private theorem prime_ninetyThreeCM_151 : Nat.Prime 151 := by norm_num

private theorem prime_ninetyThreeCM_163 : Nat.Prime 163 := by norm_num

private theorem prime_ninetyThreeCM_167 : Nat.Prime 167 := by norm_num

private theorem prime_ninetyThreeCM_173 : Nat.Prime 173 := by norm_num

private theorem prime_ninetyThreeCM_179 : Nat.Prime 179 := by norm_num

private theorem prime_ninetyThreeCM_191 : Nat.Prime 191 := by norm_num

private theorem prime_ninetyThreeCM_193 : Nat.Prime 193 := by norm_num

private theorem prime_ninetyThreeCM_197 : Nat.Prime 197 := by norm_num

private theorem prime_ninetyThreeCM_199 : Nat.Prime 199 := by norm_num

private theorem prime_ninetyThreeCM_223 : Nat.Prime 223 := by norm_num

private theorem prime_ninetyThreeCM_227 : Nat.Prime 227 := by norm_num

private theorem prime_ninetyThreeCM_229 : Nat.Prime 229 := by norm_num

private theorem prime_ninetyThreeCM_233 : Nat.Prime 233 := by norm_num

private theorem prime_ninetyThreeCM_239 : Nat.Prime 239 := by norm_num

private theorem prime_ninetyThreeCM_251 : Nat.Prime 251 := by norm_num

private theorem prime_ninetyThreeCM_263 : Nat.Prime 263 := by norm_num

private theorem prime_ninetyThreeCM_293 : Nat.Prime 293 := by norm_num

private theorem prime_ninetyThreeCM_307 : Nat.Prime 307 := by norm_num

private theorem prime_ninetyThreeCM_311 : Nat.Prime 311 := by norm_num

private theorem prime_ninetyThreeCM_313 : Nat.Prime 313 := by norm_num

private theorem prime_ninetyThreeCM_331 : Nat.Prime 331 := by norm_num

private theorem prime_ninetyThreeCM_337 : Nat.Prime 337 := by norm_num

private theorem prime_ninetyThreeCM_347 : Nat.Prime 347 := by norm_num

private theorem prime_ninetyThreeCM_349 : Nat.Prime 349 := by norm_num

private theorem prime_ninetyThreeCM_359 : Nat.Prime 359 := by norm_num

private theorem prime_ninetyThreeCM_379 : Nat.Prime 379 := by norm_num

private theorem prime_ninetyThreeCM_383 : Nat.Prime 383 := by norm_num

private theorem prime_ninetyThreeCM_397 : Nat.Prime 397 := by norm_num

private theorem prime_ninetyThreeCM_401 : Nat.Prime 401 := by norm_num

private theorem prime_ninetyThreeCM_419 : Nat.Prime 419 := by norm_num

private theorem prime_ninetyThreeCM_431 : Nat.Prime 431 := by norm_num

private theorem prime_ninetyThreeCM_439 : Nat.Prime 439 := by norm_num

private theorem prime_ninetyThreeCM_443 : Nat.Prime 443 := by norm_num

private theorem prime_ninetyThreeCM_449 : Nat.Prime 449 := by norm_num

private theorem prime_ninetyThreeCM_463 : Nat.Prime 463 := by norm_num

private theorem prime_ninetyThreeCM_509 : Nat.Prime 509 := by norm_num

private theorem prime_ninetyThreeCM_523 : Nat.Prime 523 := by norm_num

private theorem prime_ninetyThreeCM_557 : Nat.Prime 557 := by norm_num

private theorem prime_ninetyThreeCM_569 : Nat.Prime 569 := by norm_num

private theorem prime_ninetyThreeCM_587 : Nat.Prime 587 := by norm_num

private theorem prime_ninetyThreeCM_599 : Nat.Prime 599 := by norm_num

private theorem prime_ninetyThreeCM_601 : Nat.Prime 601 := by norm_num

private theorem prime_ninetyThreeCM_613 : Nat.Prime 613 := by norm_num

private theorem prime_ninetyThreeCM_617 : Nat.Prime 617 := by norm_num

private theorem prime_ninetyThreeCM_631 : Nat.Prime 631 := by norm_num

private theorem prime_ninetyThreeCM_641 : Nat.Prime 641 := by norm_num

private theorem prime_ninetyThreeCM_643 : Nat.Prime 643 := by norm_num

private theorem prime_ninetyThreeCM_647 : Nat.Prime 647 := by norm_num

private theorem prime_ninetyThreeCM_673 : Nat.Prime 673 := by norm_num

private theorem prime_ninetyThreeCM_677 : Nat.Prime 677 := by norm_num

private theorem prime_ninetyThreeCM_683 : Nat.Prime 683 := by norm_num

private theorem prime_ninetyThreeCM_719 : Nat.Prime 719 := by norm_num

private theorem prime_ninetyThreeCM_727 : Nat.Prime 727 := by norm_num

private theorem prime_ninetyThreeCM_743 : Nat.Prime 743 := by norm_num

private theorem prime_ninetyThreeCM_751 : Nat.Prime 751 := by norm_num

private theorem prime_ninetyThreeCM_757 : Nat.Prime 757 := by norm_num

private theorem prime_ninetyThreeCM_773 : Nat.Prime 773 := by norm_num

private theorem prime_ninetyThreeCM_809 : Nat.Prime 809 := by norm_num

private theorem prime_ninetyThreeCM_821 : Nat.Prime 821 := by norm_num

private theorem prime_ninetyThreeCM_839 : Nat.Prime 839 := by norm_num

private theorem prime_ninetyThreeCM_853 : Nat.Prime 853 := by norm_num

private theorem prime_ninetyThreeCM_881 : Nat.Prime 881 := by norm_num

private theorem prime_ninetyThreeCM_883 : Nat.Prime 883 := by norm_num

private theorem prime_ninetyThreeCM_971 : Nat.Prime 971 := by norm_num

private theorem prime_ninetyThreeCM_983 : Nat.Prime 983 := by norm_num

private theorem prime_ninetyThreeCM_997 : Nat.Prime 997 := by norm_num

private theorem prime_ninetyThreeCM_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_ninetyThreeCM_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_ninetyThreeCM_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_ninetyThreeCM_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_ninetyThreeCM_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_ninetyThreeCM_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_ninetyThreeCM_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_ninetyThreeCM_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_ninetyThreeCM_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_ninetyThreeCM_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_ninetyThreeCM_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_ninetyThreeCM_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_ninetyThreeCM_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_ninetyThreeCM_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_ninetyThreeCM_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_ninetyThreeCM_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_ninetyThreeCM_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_ninetyThreeCM_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_ninetyThreeCM_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_ninetyThreeCM_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_ninetyThreeCM_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_ninetyThreeCM_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_ninetyThreeCM_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_ninetyThreeCM_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_ninetyThreeCM_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_ninetyThreeCM_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_ninetyThreeCM_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_ninetyThreeCM_2341 : Nat.Prime 2341 := by norm_num

private theorem prime_ninetyThreeCM_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_ninetyThreeCM_2371 : Nat.Prime 2371 := by norm_num

private theorem prime_ninetyThreeCM_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_ninetyThreeCM_2417 : Nat.Prime 2417 := by norm_num

private theorem prime_ninetyThreeCM_2437 : Nat.Prime 2437 := by norm_num

private theorem prime_ninetyThreeCM_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_ninetyThreeCM_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_ninetyThreeCM_2683 : Nat.Prime 2683 := by norm_num

private theorem prime_ninetyThreeCM_2707 : Nat.Prime 2707 := by norm_num

private theorem prime_ninetyThreeCM_2791 : Nat.Prime 2791 := by norm_num

private theorem prime_ninetyThreeCM_2861 : Nat.Prime 2861 := by norm_num

private theorem prime_ninetyThreeCM_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_ninetyThreeCM_2971 : Nat.Prime 2971 := by norm_num

private theorem prime_ninetyThreeCM_3083 : Nat.Prime 3083 := by norm_num

private theorem prime_ninetyThreeCM_3163 : Nat.Prime 3163 := by norm_num

private theorem prime_ninetyThreeCM_3191 : Nat.Prime 3191 := by norm_num

private theorem prime_ninetyThreeCM_3209 : Nat.Prime 3209 := by norm_num

private theorem prime_ninetyThreeCM_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_ninetyThreeCM_3307 : Nat.Prime 3307 := by norm_num

private theorem prime_ninetyThreeCM_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_ninetyThreeCM_3329 : Nat.Prime 3329 := by norm_num

private theorem prime_ninetyThreeCM_3361 : Nat.Prime 3361 := by norm_num

private theorem prime_ninetyThreeCM_3491 : Nat.Prime 3491 := by norm_num

private theorem prime_ninetyThreeCM_3527 : Nat.Prime 3527 := by norm_num

private theorem prime_ninetyThreeCM_3529 : Nat.Prime 3529 := by norm_num

private theorem prime_ninetyThreeCM_3659 : Nat.Prime 3659 := by norm_num

private theorem prime_ninetyThreeCM_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_ninetyThreeCM_3727 : Nat.Prime 3727 := by norm_num

private theorem prime_ninetyThreeCM_3863 : Nat.Prime 3863 := by norm_num

private theorem prime_ninetyThreeCM_3877 : Nat.Prime 3877 := by norm_num

private theorem prime_ninetyThreeCM_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_ninetyThreeCM_3943 : Nat.Prime 3943 := by norm_num

private theorem prime_ninetyThreeCM_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_ninetyThreeCM_4159 : Nat.Prime 4159 := by norm_num

private theorem prime_ninetyThreeCM_4337 : Nat.Prime 4337 := by norm_num

private theorem prime_ninetyThreeCM_4513 : Nat.Prime 4513 := by norm_num

private theorem prime_ninetyThreeCM_4987 : Nat.Prime 4987 := by norm_num

private theorem prime_ninetyThreeCM_5003 : Nat.Prime 5003 := by norm_num

private theorem prime_ninetyThreeCM_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_ninetyThreeCM_5279 : Nat.Prime 5279 := by norm_num

private theorem prime_ninetyThreeCM_5399 : Nat.Prime 5399 := by norm_num

private theorem prime_ninetyThreeCM_5413 : Nat.Prime 5413 := by norm_num

private theorem prime_ninetyThreeCM_5501 : Nat.Prime 5501 := by norm_num

private theorem prime_ninetyThreeCM_5581 : Nat.Prime 5581 := by norm_num

private theorem prime_ninetyThreeCM_5801 : Nat.Prime 5801 := by norm_num

private theorem prime_ninetyThreeCM_5813 : Nat.Prime 5813 := by norm_num

private theorem prime_ninetyThreeCM_5869 : Nat.Prime 5869 := by norm_num

private theorem prime_ninetyThreeCM_6089 : Nat.Prime 6089 := by norm_num

private theorem prime_ninetyThreeCM_6131 : Nat.Prime 6131 := by norm_num

private theorem prime_ninetyThreeCM_6211 : Nat.Prime 6211 := by norm_num

private theorem prime_ninetyThreeCM_6317 : Nat.Prime 6317 := by norm_num

private theorem prime_ninetyThreeCM_6563 : Nat.Prime 6563 := by norm_num

private theorem prime_ninetyThreeCM_6733 : Nat.Prime 6733 := by norm_num

private theorem prime_ninetyThreeCM_7121 : Nat.Prime 7121 := by norm_num

private theorem prime_ninetyThreeCM_7489 : Nat.Prime 7489 := by norm_num

private theorem prime_ninetyThreeCM_7537 : Nat.Prime 7537 := by norm_num

private theorem prime_ninetyThreeCM_7699 : Nat.Prime 7699 := by norm_num

private theorem prime_ninetyThreeCM_7741 : Nat.Prime 7741 := by norm_num

private theorem prime_ninetyThreeCM_7927 : Nat.Prime 7927 := by norm_num

private theorem prime_ninetyThreeCM_7993 : Nat.Prime 7993 := by norm_num

private theorem prime_ninetyThreeCM_8209 : Nat.Prime 8209 := by norm_num

private theorem prime_ninetyThreeCM_8233 : Nat.Prime 8233 := by norm_num

private theorem prime_ninetyThreeCM_8317 : Nat.Prime 8317 := by norm_num

private theorem prime_ninetyThreeCM_8461 : Nat.Prime 8461 := by norm_num

private theorem prime_ninetyThreeCM_8663 : Nat.Prime 8663 := by norm_num

private theorem prime_ninetyThreeCM_8849 : Nat.Prime 8849 := by norm_num

private theorem prime_ninetyThreeCM_8893 : Nat.Prime 8893 := by norm_num

private theorem prime_ninetyThreeCM_9437 : Nat.Prime 9437 := by norm_num

private theorem prime_ninetyThreeCM_9511 : Nat.Prime 9511 := by norm_num

private theorem prime_ninetyThreeCM_9833 : Nat.Prime 9833 := by norm_num

private theorem prime_ninetyThreeCM_9839 : Nat.Prime 9839 := by norm_num

private theorem prime_ninetyThreeCM_9931 : Nat.Prime 9931 := by norm_num

private theorem prime_ninetyThreeCM_10529 : Nat.Prime 10529 := by norm_num

private theorem prime_ninetyThreeCM_11083 : Nat.Prime 11083 := by norm_num

private theorem prime_ninetyThreeCM_11801 : Nat.Prime 11801 := by norm_num

private theorem prime_ninetyThreeCM_12517 : Nat.Prime 12517 := by norm_num

private theorem prime_ninetyThreeCM_12671 : Nat.Prime 12671 := by norm_num

private theorem prime_ninetyThreeCM_13043 : Nat.Prime 13043 := by norm_num

private theorem prime_ninetyThreeCM_13313 : Nat.Prime 13313 := by norm_num

private theorem prime_ninetyThreeCM_13567 : Nat.Prime 13567 := by norm_num

private theorem prime_ninetyThreeCM_14723 : Nat.Prime 14723 := by norm_num

private theorem prime_ninetyThreeCM_15749 : Nat.Prime 15749 := by norm_num

private theorem prime_ninetyThreeCM_15797 : Nat.Prime 15797 := by norm_num

private theorem prime_ninetyThreeCM_15889 : Nat.Prime 15889 := by norm_num

private theorem prime_ninetyThreeCM_16061 : Nat.Prime 16061 := by norm_num

private theorem prime_ninetyThreeCM_16561 : Nat.Prime 16561 := by norm_num

private theorem prime_ninetyThreeCM_16567 : Nat.Prime 16567 := by norm_num

private theorem prime_ninetyThreeCM_16633 : Nat.Prime 16633 := by norm_num

private theorem prime_ninetyThreeCM_17539 : Nat.Prime 17539 := by norm_num

private theorem prime_ninetyThreeCM_17837 : Nat.Prime 17837 := by norm_num

private theorem prime_ninetyThreeCM_18731 : Nat.Prime 18731 := by norm_num

private theorem prime_ninetyThreeCM_18797 : Nat.Prime 18797 := by norm_num

private theorem prime_ninetyThreeCM_19037 : Nat.Prime 19037 := by norm_num

private theorem prime_ninetyThreeCM_19867 : Nat.Prime 19867 := by norm_num

private theorem prime_ninetyThreeCM_20261 : Nat.Prime 20261 := by norm_num

private theorem prime_ninetyThreeCM_20887 : Nat.Prime 20887 := by norm_num

private theorem prime_ninetyThreeCM_22013 : Nat.Prime 22013 := by norm_num

private theorem prime_ninetyThreeCM_23099 : Nat.Prime 23099 := by norm_num

private theorem prime_ninetyThreeCM_24733 : Nat.Prime 24733 := by norm_num

private theorem prime_ninetyThreeCM_26107 : Nat.Prime 26107 := by norm_num

private theorem prime_ninetyThreeCM_26561 : Nat.Prime 26561 := by norm_num

private theorem prime_ninetyThreeCM_26921 : Nat.Prime 26921 := by norm_num

private theorem prime_ninetyThreeCM_27697 : Nat.Prime 27697 := by norm_num

private theorem prime_ninetyThreeCM_28319 : Nat.Prime 28319 := by norm_num

private theorem prime_ninetyThreeCM_29129 : Nat.Prime 29129 := by norm_num

private theorem prime_ninetyThreeCM_29531 : Nat.Prime 29531 := by norm_num

private theorem prime_ninetyThreeCM_30323 : Nat.Prime 30323 := by norm_num

private theorem prime_ninetyThreeCM_33317 : Nat.Prime 33317 := by norm_num

private theorem prime_ninetyThreeCM_34721 : Nat.Prime 34721 := by norm_num

private theorem prime_ninetyThreeCM_35573 : Nat.Prime 35573 := by norm_num

private theorem prime_ninetyThreeCM_38461 : Nat.Prime 38461 := by norm_num

private theorem prime_ninetyThreeCM_38557 : Nat.Prime 38557 := by norm_num

private theorem prime_ninetyThreeCM_41227 : Nat.Prime 41227 := by norm_num

private theorem prime_ninetyThreeCM_43207 : Nat.Prime 43207 := by norm_num

private theorem prime_ninetyThreeCM_45667 : Nat.Prime 45667 := by norm_num

private theorem prime_ninetyThreeCM_46663 : Nat.Prime 46663 := by norm_num

private theorem prime_ninetyThreeCM_46681 : Nat.Prime 46681 := by norm_num

private theorem prime_ninetyThreeCM_49811 : Nat.Prime 49811 := by norm_num

private theorem prime_ninetyThreeCM_51283 : Nat.Prime 51283 := by norm_num

private theorem prime_ninetyThreeCM_51871 : Nat.Prime 51871 := by norm_num

private theorem prime_ninetyThreeCM_52361 : Nat.Prime 52361 := by norm_num

private theorem prime_ninetyThreeCM_55207 : Nat.Prime 55207 := by norm_num

private theorem prime_ninetyThreeCM_58481 : Nat.Prime 58481 := by norm_num

private theorem prime_ninetyThreeCM_59159 : Nat.Prime 59159 := by norm_num

private theorem prime_ninetyThreeCM_59753 : Nat.Prime 59753 := by norm_num

private theorem prime_ninetyThreeCM_60413 : Nat.Prime 60413 := by norm_num

private theorem prime_ninetyThreeCM_60601 : Nat.Prime 60601 := by norm_num

private theorem prime_ninetyThreeCM_63247 : Nat.Prime 63247 := by norm_num

private theorem prime_ninetyThreeCM_64709 : Nat.Prime 64709 := by norm_num

private theorem prime_ninetyThreeCM_65327 : Nat.Prime 65327 := by norm_num

private theorem prime_ninetyThreeCM_70549 : Nat.Prime 70549 := by norm_num

private theorem prime_ninetyThreeCM_77659 : Nat.Prime 77659 := by norm_num

private theorem prime_ninetyThreeCM_80789 : Nat.Prime 80789 := by norm_num

private theorem prime_ninetyThreeCM_86161 : Nat.Prime 86161 := by norm_num

private theorem prime_ninetyThreeCM_87643 : Nat.Prime 87643 := by norm_num

private theorem prime_ninetyThreeCM_98143 : Nat.Prime 98143 := by norm_num

private theorem prime_ninetyThreeCM_99109 : Nat.Prime 99109 := by norm_num

private theorem prime_ninetyThreeCM_100103 : Nat.Prime 100103 := by norm_num

private theorem prime_ninetyThreeCM_111103 : Nat.Prime 111103 := by norm_num

private theorem prime_ninetyThreeCM_128431 : Nat.Prime 128431 := by norm_num

private theorem prime_ninetyThreeCM_131431 : Nat.Prime 131431 := by norm_num

private theorem prime_ninetyThreeCM_134681 : Nat.Prime 134681 := by norm_num

private theorem prime_ninetyThreeCM_135151 : Nat.Prime 135151 := by norm_num

private theorem prime_ninetyThreeCM_139387 : Nat.Prime 139387 := by norm_num

private theorem prime_ninetyThreeCM_142469 : Nat.Prime 142469 := by norm_num

private theorem prime_ninetyThreeCM_145283 : Nat.Prime 145283 := by norm_num

private theorem prime_ninetyThreeCM_149027 : Nat.Prime 149027 := by norm_num

private theorem prime_ninetyThreeCM_156241 : Nat.Prime 156241 := by norm_num

private theorem prime_ninetyThreeCM_174649 : Nat.Prime 174649 := by norm_num

private theorem prime_ninetyThreeCM_175691 : Nat.Prime 175691 := by norm_num

private theorem prime_ninetyThreeCM_196751 : Nat.Prime 196751 := by norm_num

private theorem prime_ninetyThreeCM_204431 : Nat.Prime 204431 := by norm_num

private theorem prime_ninetyThreeCM_208961 : Nat.Prime 208961 := by norm_num

private theorem prime_ninetyThreeCM_219707 : Nat.Prime 219707 := by norm_num

private theorem prime_ninetyThreeCM_236219 : Nat.Prime 236219 := by norm_num

private theorem prime_ninetyThreeCM_240859 : Nat.Prime 240859 := by norm_num

private theorem prime_ninetyThreeCM_252667 : Nat.Prime 252667 := by norm_num

private theorem prime_ninetyThreeCM_253447 : Nat.Prime 253447 := by norm_num

private theorem prime_ninetyThreeCM_255371 : Nat.Prime 255371 := by norm_num

private theorem prime_ninetyThreeCM_255859 : Nat.Prime 255859 := by norm_num

private theorem prime_ninetyThreeCM_255971 : Nat.Prime 255971 := by norm_num

private theorem prime_ninetyThreeCM_261847 : Nat.Prime 261847 := by norm_num

private theorem prime_ninetyThreeCM_265339 : Nat.Prime 265339 := by norm_num

private theorem prime_ninetyThreeCM_271181 : Nat.Prime 271181 := by norm_num

private theorem prime_ninetyThreeCM_272539 : Nat.Prime 272539 := by norm_num

private theorem prime_ninetyThreeCM_274349 : Nat.Prime 274349 := by norm_num

private theorem prime_ninetyThreeCM_312469 : Nat.Prime 312469 := by norm_num

private theorem prime_ninetyThreeCM_320843 : Nat.Prime 320843 := by norm_num

private theorem prime_ninetyThreeCM_321187 : Nat.Prime 321187 := by norm_num

private theorem prime_ninetyThreeCM_375371 : Nat.Prime 375371 := by norm_num

private theorem prime_ninetyThreeCM_380047 : Nat.Prime 380047 := by norm_num

private theorem prime_ninetyThreeCM_402107 : Nat.Prime 402107 := by norm_num

private theorem prime_ninetyThreeCM_464993 : Nat.Prime 464993 := by norm_num

private theorem prime_ninetyThreeCM_474533 : Nat.Prime 474533 := by norm_num

private theorem prime_ninetyThreeCM_502643 : Nat.Prime 502643 := by norm_num

private theorem prime_ninetyThreeCM_513053 : Nat.Prime 513053 := by norm_num

private theorem prime_ninetyThreeCM_530539 : Nat.Prime 530539 := by norm_num

private theorem prime_ninetyThreeCM_531331 : Nat.Prime 531331 := by norm_num

private theorem prime_ninetyThreeCM_574393 : Nat.Prime 574393 := by norm_num

private theorem prime_ninetyThreeCM_632911 : Nat.Prime 632911 := by norm_num

private theorem prime_ninetyThreeCM_712819 : Nat.Prime 712819 := by norm_num

private theorem prime_ninetyThreeCM_777181 : Nat.Prime 777181 := by norm_num

private theorem prime_ninetyThreeCM_781117 : Nat.Prime 781117 := by norm_num

private theorem prime_ninetyThreeCM_806543 : Nat.Prime 806543 := by norm_num

private theorem prime_ninetyThreeCM_824459 : Nat.Prime 824459 := by norm_num

private theorem prime_ninetyThreeCM_826381 : Nat.Prime 826381 := by norm_num

private theorem prime_ninetyThreeCM_852323 : Nat.Prime 852323 := by norm_num

private theorem prime_ninetyThreeCM_900797 : Nat.Prime 900797 := by norm_num

private theorem prime_ninetyThreeCM_916649 : Nat.Prime 916649 := by norm_num

private theorem prime_ninetyThreeCM_940787 : Nat.Prime 940787 := by norm_num

private theorem prime_ninetyThreeCM_950633 : Nat.Prime 950633 := by norm_num

private theorem prime_ninetyThreeCM_981173 : Nat.Prime 981173 := by norm_num

private theorem prime_ninetyThreeCM_1018643 : Nat.Prime 1018643 := by norm_num

private theorem prime_ninetyThreeCM_1055809 : Nat.Prime 1055809 := by norm_num

private theorem prime_ninetyThreeCM_1060201 : Nat.Prime 1060201 := by norm_num

private theorem prime_ninetyThreeCM_1064411 : Nat.Prime 1064411 := by norm_num

private theorem prime_ninetyThreeCM_1073857 : Nat.Prime 1073857 := by norm_num

private theorem prime_ninetyThreeCM_1199329 : Nat.Prime 1199329 := by norm_num

private theorem prime_ninetyThreeCM_1220489 : Nat.Prime 1220489 := by norm_num

private theorem prime_ninetyThreeCM_1303013 : Nat.Prime 1303013 := by norm_num

private theorem prime_ninetyThreeCM_1333867 : Nat.Prime 1333867 := by norm_num

private theorem prime_ninetyThreeCM_1376257 : Nat.Prime 1376257 := by norm_num

private theorem prime_ninetyThreeCM_1444447 : Nat.Prime 1444447 := by norm_num

private theorem prime_ninetyThreeCM_1456313 : Nat.Prime 1456313 := by norm_num

private theorem prime_ninetyThreeCM_1461139 : Nat.Prime 1461139 := by norm_num

private theorem prime_ninetyThreeCM_1507039 : Nat.Prime 1507039 := by norm_num

private theorem prime_ninetyThreeCM_1572521 : Nat.Prime 1572521 := by norm_num

private theorem prime_ninetyThreeCM_1653499 : Nat.Prime 1653499 := by norm_num

private theorem prime_ninetyThreeCM_1667837 : Nat.Prime 1667837 := by norm_num

private theorem prime_ninetyThreeCM_1709789 : Nat.Prime 1709789 := by norm_num

private theorem prime_ninetyThreeCM_1826519 : Nat.Prime 1826519 := by norm_num

private theorem prime_ninetyThreeCM_1879921 : Nat.Prime 1879921 := by norm_num

private theorem prime_ninetyThreeCM_2058839 : Nat.Prime 2058839 := by norm_num

private theorem prime_ninetyThreeCM_2177891 : Nat.Prime 2177891 := by norm_num

private theorem prime_ninetyThreeCM_2214383 : Nat.Prime 2214383 := by norm_num

private theorem prime_ninetyThreeCM_2467351 : Nat.Prime 2467351 := by norm_num

private theorem prime_ninetyThreeCM_2567683 : Nat.Prime 2567683 := by norm_num

private theorem prime_ninetyThreeCM_2950517 : Nat.Prime 2950517 := by norm_num

private theorem prime_ninetyThreeCM_3058879 : Nat.Prime 3058879 := by norm_num

private theorem prime_ninetyThreeCM_3196511 : Nat.Prime 3196511 := by norm_num

private theorem prime_ninetyThreeCM_3309167 : Nat.Prime 3309167 := by norm_num

private theorem prime_ninetyThreeCM_3322757 : Nat.Prime 3322757 := by norm_num

private theorem prime_ninetyThreeCM_3396551 : Nat.Prime 3396551 := by norm_num

private theorem prime_ninetyThreeCM_3451963 : Nat.Prime 3451963 := by norm_num

private theorem prime_ninetyThreeCM_3727753 : Nat.Prime 3727753 := by norm_num

private theorem prime_ninetyThreeCM_4470803 : Nat.Prime 4470803 := by norm_num

private theorem prime_ninetyThreeCM_4475837 : Nat.Prime 4475837 := by norm_num

private theorem prime_ninetyThreeCM_4504369 : Nat.Prime 4504369 := by norm_num

private theorem prime_ninetyThreeCM_4507339 : Nat.Prime 4507339 := by norm_num

private theorem prime_ninetyThreeCM_5091887 : Nat.Prime 5091887 := by norm_num

private theorem prime_ninetyThreeCM_5254351 : Nat.Prime 5254351 := by norm_num

private theorem prime_ninetyThreeCM_5314783 : Nat.Prime 5314783 := by norm_num

private theorem prime_ninetyThreeCM_5367667 : Nat.Prime 5367667 := by norm_num

private theorem prime_ninetyThreeCM_5579773 : Nat.Prime 5579773 := by norm_num

private theorem prime_ninetyThreeCM_5674181 : Nat.Prime 5674181 := by norm_num

private theorem prime_ninetyThreeCM_5687999 : Nat.Prime 5687999 := by norm_num

private theorem prime_ninetyThreeCM_5950067 : Nat.Prime 5950067 := by norm_num

private theorem prime_ninetyThreeCM_6330407 : Nat.Prime 6330407 := by norm_num

private theorem prime_ninetyThreeCM_6349223 : Nat.Prime 6349223 := by norm_num

private theorem prime_ninetyThreeCM_6393229 : Nat.Prime 6393229 := by norm_num

private theorem prime_ninetyThreeCM_7346827 : Nat.Prime 7346827 := by norm_num

private theorem prime_ninetyThreeCM_7395413 : Nat.Prime 7395413 := by norm_num

private theorem prime_ninetyThreeCM_7889341 : Nat.Prime 7889341 := by norm_num

private theorem prime_ninetyThreeCM_7949839 : Nat.Prime 7949839 := by norm_num

private theorem prime_ninetyThreeCM_8012057 : Nat.Prime 8012057 := by norm_num

private theorem prime_ninetyThreeCM_8052433 : Nat.Prime 8052433 := by norm_num

private theorem prime_ninetyThreeCM_8107787 : Nat.Prime 8107787 := by norm_num

private theorem prime_ninetyThreeCM_9290167 : Nat.Prime 9290167 := by norm_num

private theorem prime_ninetyThreeCM_9319333 : Nat.Prime 9319333 := by norm_num

private theorem prime_ninetyThreeCM_9554123 : Nat.Prime 9554123 := by norm_num

private theorem prime_ninetyThreeCM_9919447 : Nat.Prime 9919447 := by norm_num

private theorem prime_ninetyThreeCM_10033091 : Nat.Prime 10033091 := by norm_num

private theorem prime_ninetyThreeCM_10122491 : Nat.Prime 10122491 := by norm_num

private theorem prime_ninetyThreeCM_10578521 : Nat.Prime 10578521 := by norm_num

private theorem prime_ninetyThreeCM_10725943 : Nat.Prime 10725943 := by norm_num

private theorem prime_ninetyThreeCM_10907089 : Nat.Prime 10907089 := by norm_num

private theorem prime_ninetyThreeCM_10912009 : Nat.Prime 10912009 := by norm_num

private theorem prime_ninetyThreeCM_12319609 : Nat.Prime 12319609 := by norm_num

private theorem prime_ninetyThreeCM_12337727 : Nat.Prime 12337727 := by norm_num

private theorem prime_ninetyThreeCM_12362221 : Nat.Prime 12362221 := by norm_num

private theorem prime_ninetyThreeCM_12764513 : Nat.Prime 12764513 := by norm_num

private theorem prime_ninetyThreeCM_12870493 : Nat.Prime 12870493 := by norm_num

private theorem prime_ninetyThreeCM_13282123 : Nat.Prime 13282123 := by norm_num

private theorem prime_ninetyThreeCM_13388761 : Nat.Prime 13388761 := by norm_num

private theorem prime_ninetyThreeCM_15877013 : Nat.Prime 15877013 := by norm_num

private theorem prime_ninetyThreeCM_16140017 : Nat.Prime 16140017 := by norm_num

private theorem prime_ninetyThreeCM_16543361 : Nat.Prime 16543361 := by norm_num

private theorem prime_ninetyThreeCM_16765193 : Nat.Prime 16765193 := by norm_num

private theorem prime_ninetyThreeCM_17399171 : Nat.Prime 17399171 := by norm_num

private theorem prime_ninetyThreeCM_17663447 : Nat.Prime 17663447 := by norm_num

private theorem prime_ninetyThreeCM_17903443 : Nat.Prime 17903443 := by norm_num

private theorem prime_ninetyThreeCM_18031483 : Nat.Prime 18031483 := by norm_num

private theorem prime_ninetyThreeCM_18886499 : Nat.Prime 18886499 := by norm_num

private theorem prime_ninetyThreeCM_19978837 : Nat.Prime 19978837 := by norm_num

private theorem prime_ninetyThreeCM_20996369 : Nat.Prime 20996369 := by norm_num

private theorem prime_ninetyThreeCM_21786781 : Nat.Prime 21786781 := by norm_num

private theorem prime_ninetyThreeCM_22780973 : Nat.Prime 22780973 := by norm_num

private theorem prime_ninetyThreeCM_22834517 : Nat.Prime 22834517 := by norm_num

private theorem prime_ninetyThreeCM_23453957 : Nat.Prime 23453957 := by norm_num

private theorem prime_ninetyThreeCM_24390337 : Nat.Prime 24390337 := by norm_num

private theorem prime_ninetyThreeCM_25409141 : Nat.Prime 25409141 := by norm_num

private theorem prime_ninetyThreeCM_25840723 : Nat.Prime 25840723 := by norm_num

private theorem prime_ninetyThreeCM_26140139 : Nat.Prime 26140139 := by norm_num

private theorem prime_ninetyThreeCM_26317517 : Nat.Prime 26317517 := by norm_num

private theorem prime_ninetyThreeCM_27960473 : Nat.Prime 27960473 := by norm_num

private theorem prime_ninetyThreeCM_29432047 : Nat.Prime 29432047 := by norm_num

private theorem prime_ninetyThreeCM_30952531 : Nat.Prime 30952531 := by
  apply lucas_primality 30952531 (2 : ZMod 30952531)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (7, 1), (53, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (7, 1), (53, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) = 30952531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_53
      · exact prime_ninetyThreeCM_103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30952531) ^ 15476265 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30952531) ^ 10317510 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30952531) ^ 6190506 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30952531) ^ 4421790 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30952531) ^ 584010 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30952531) ^ 300510 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_32830249 : Nat.Prime 32830249 := by
  apply lucas_primality 32830249 (43 : ZMod 32830249)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (37, 1), (3361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (37, 1), (3361, 1)] : List FactorBlock).map factorBlockValue).prod) = 32830249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_37
      · exact prime_ninetyThreeCM_3361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (43 : ZMod 32830249) ^ 16415124 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (43 : ZMod 32830249) ^ 10943416 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (43 : ZMod 32830249) ^ 2984568 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (43 : ZMod 32830249) ^ 887304 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (43 : ZMod 32830249) ^ 9768 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_33471533 : Nat.Prime 33471533 := by
  apply lucas_primality 33471533 (2 : ZMod 33471533)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (37, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (37, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod) = 33471533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_23
      · exact prime_ninetyThreeCM_37
      · exact prime_ninetyThreeCM_9833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33471533) ^ 16735766 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33471533) ^ 1455284 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33471533) ^ 904636 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33471533) ^ 3404 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_34122887 : Nat.Prime 34122887 := by
  apply lucas_primality 34122887 (5 : ZMod 34122887)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (109, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (109, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) = 34122887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_59
      · exact prime_ninetyThreeCM_109
      · exact prime_ninetyThreeCM_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 34122887) ^ 17061443 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 34122887) ^ 4874698 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 34122887) ^ 578354 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 34122887) ^ 313054 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 34122887) ^ 90034 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_37280797 : Nat.Prime 37280797 := by
  apply lucas_primality 37280797 (2 : ZMod 37280797)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (26107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (26107, 1)] : List FactorBlock).map factorBlockValue).prod) = 37280797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_26107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37280797) ^ 18640398 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 37280797) ^ 12426932 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 37280797) ^ 5325828 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 37280797) ^ 2192988 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 37280797) ^ 1428 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_40094183 : Nat.Prime 40094183 := by
  apply lucas_primality 40094183 (5 : ZMod 40094183)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (53, 1), (13043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (53, 1), (13043, 1)] : List FactorBlock).map factorBlockValue).prod) = 40094183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_53
      · exact prime_ninetyThreeCM_13043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 40094183) ^ 20047091 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 40094183) ^ 1382558 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 40094183) ^ 756494 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 40094183) ^ 3074 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_48646723 : Nat.Prime 48646723 := by
  apply lucas_primality 48646723 (5 : ZMod 48646723)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8107787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8107787, 1)] : List FactorBlock).map factorBlockValue).prod) = 48646723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_8107787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 48646723) ^ 24323361 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48646723) ^ 16215574 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 48646723) ^ 6 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_50818283 : Nat.Prime 50818283 := by
  apply lucas_primality 50818283 (2 : ZMod 50818283)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25409141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25409141, 1)] : List FactorBlock).map factorBlockValue).prod) = 50818283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_25409141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 50818283) ^ 25409141 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 50818283) ^ 2 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_51036959 : Nat.Prime 51036959 := by
  apply lucas_primality 51036959 (7 : ZMod 51036959)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (43, 1), (4987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (43, 1), (4987, 1)] : List FactorBlock).map factorBlockValue).prod) = 51036959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_43
      · exact prime_ninetyThreeCM_4987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 51036959) ^ 25518479 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 51036959) ^ 7290994 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 51036959) ^ 3002174 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 51036959) ^ 1186906 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 51036959) ^ 10234 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_55013381 : Nat.Prime 55013381 := by
  apply lucas_primality 55013381 (2 : ZMod 55013381)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (347, 1), (7927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (347, 1), (7927, 1)] : List FactorBlock).map factorBlockValue).prod) = 55013381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_347
      · exact prime_ninetyThreeCM_7927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55013381) ^ 27506690 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 55013381) ^ 11002676 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 55013381) ^ 158540 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 55013381) ^ 6940 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_58884443 : Nat.Prime 58884443 := by
  apply lucas_primality 58884443 (2 : ZMod 58884443)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (307, 1), (3307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (307, 1), (3307, 1)] : List FactorBlock).map factorBlockValue).prod) = 58884443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_307
      · exact prime_ninetyThreeCM_3307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58884443) ^ 29442221 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 58884443) ^ 2030498 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 58884443) ^ 191806 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 58884443) ^ 17806 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_59999627 : Nat.Prime 59999627 := by
  apply lucas_primality 59999627 (2 : ZMod 59999627)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (236219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (236219, 1)] : List FactorBlock).map factorBlockValue).prod) = 59999627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_127
      · exact prime_ninetyThreeCM_236219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59999627) ^ 29999813 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 59999627) ^ 472438 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 59999627) ^ 254 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_60813239 : Nat.Prime 60813239 := by
  apply lucas_primality 60813239 (7 : ZMod 60813239)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (431, 1), (70549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (431, 1), (70549, 1)] : List FactorBlock).map factorBlockValue).prod) = 60813239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_431
      · exact prime_ninetyThreeCM_70549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 60813239) ^ 30406619 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 60813239) ^ 141098 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 60813239) ^ 862 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_61074289 : Nat.Prime 61074289 := by
  apply lucas_primality 61074289 (7 : ZMod 61074289)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (11, 1), (38557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (11, 1), (38557, 1)] : List FactorBlock).map factorBlockValue).prod) = 61074289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_38557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 61074289) ^ 30537144 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 61074289) ^ 20358096 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 61074289) ^ 5552208 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 61074289) ^ 1584 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_64872481 : Nat.Prime 64872481 := by
  apply lucas_primality 64872481 (23 : ZMod 64872481)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (135151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (135151, 1)] : List FactorBlock).map factorBlockValue).prod) = 64872481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_135151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 64872481) ^ 32436240 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (23 : ZMod 64872481) ^ 21624160 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (23 : ZMod 64872481) ^ 12974496 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (23 : ZMod 64872481) ^ 480 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_66943067 : Nat.Prime 66943067 := by
  apply lucas_primality 66943067 (2 : ZMod 66943067)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (33471533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (33471533, 1)] : List FactorBlock).map factorBlockValue).prod) = 66943067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_33471533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 66943067) ^ 33471533 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66943067) ^ 2 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_70249271 : Nat.Prime 70249271 := by
  apply lucas_primality 70249271 (14 : ZMod 70249271)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (17, 1), (19, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (17, 1), (19, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 70249271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 70249271) ^ 35124635 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (14 : ZMod 70249271) ^ 14049854 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (14 : ZMod 70249271) ^ 10035610 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (14 : ZMod 70249271) ^ 5403790 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (14 : ZMod 70249271) ^ 4132310 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (14 : ZMod 70249271) ^ 3697330 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (14 : ZMod 70249271) ^ 293930 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_76620931 : Nat.Prime 76620931 := by
  apply lucas_primality 76620931 (2 : ZMod 76620931)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1091, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1091, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) = 76620931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_1091
      · exact prime_ninetyThreeCM_2341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76620931) ^ 38310465 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76620931) ^ 25540310 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76620931) ^ 15324186 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76620931) ^ 70230 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76620931) ^ 32730 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_77740511 : Nat.Prime 77740511 := by
  apply lucas_primality 77740511 (7 : ZMod 77740511)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (127, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (127, 1), (1493, 1)] : List FactorBlock).map factorBlockValue).prod) = 77740511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_41
      · exact prime_ninetyThreeCM_127
      · exact prime_ninetyThreeCM_1493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 77740511) ^ 38870255 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 77740511) ^ 15548102 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 77740511) ^ 1896110 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 77740511) ^ 612130 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 77740511) ^ 52070 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_82866247 : Nat.Prime 82866247 := by
  apply lucas_primality 82866247 (3 : ZMod 82866247)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (321187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (321187, 1)] : List FactorBlock).map factorBlockValue).prod) = 82866247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_43
      · exact prime_ninetyThreeCM_321187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 82866247) ^ 41433123 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 82866247) ^ 27622082 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 82866247) ^ 1927122 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 82866247) ^ 258 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_84111409 : Nat.Prime 84111409 := by
  apply lucas_primality 84111409 (11 : ZMod 84111409)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (89, 1), (6563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (89, 1), (6563, 1)] : List FactorBlock).map factorBlockValue).prod) = 84111409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_89
      · exact prime_ninetyThreeCM_6563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 84111409) ^ 42055704 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 84111409) ^ 28037136 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 84111409) ^ 945072 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 84111409) ^ 12816 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_88285003 : Nat.Prime 88285003 := by
  apply lucas_primality 88285003 (3 : ZMod 88285003)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (293, 1), (3863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (293, 1), (3863, 1)] : List FactorBlock).map factorBlockValue).prod) = 88285003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_293
      · exact prime_ninetyThreeCM_3863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88285003) ^ 44142501 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 88285003) ^ 29428334 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 88285003) ^ 6791154 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 88285003) ^ 301314 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 88285003) ^ 22854 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_89010637 : Nat.Prime 89010637 := by
  apply lucas_primality 89010637 (2 : ZMod 89010637)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (51871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (51871, 1)] : List FactorBlock).map factorBlockValue).prod) = 89010637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_51871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89010637) ^ 44505318 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 89010637) ^ 29670212 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 89010637) ^ 8091876 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 89010637) ^ 6846972 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 89010637) ^ 1716 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_93649217 : Nat.Prime 93649217 := by
  apply lucas_primality 93649217 (3 : ZMod 93649217)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (1123, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (1123, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) = 93649217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_1123
      · exact prime_ninetyThreeCM_1303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 93649217) ^ 46824608 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 93649217) ^ 83392 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 93649217) ^ 71872 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_94693237 : Nat.Prime 94693237 := by
  apply lucas_primality 94693237 (35 : ZMod 94693237)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (29, 2), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (29, 2), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 94693237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (35 : ZMod 94693237) ^ 47346618 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (35 : ZMod 94693237) ^ 31564412 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (35 : ZMod 94693237) ^ 8608476 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (35 : ZMod 94693237) ^ 3265284 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (35 : ZMod 94693237) ^ 111012 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_101054771 : Nat.Prime 101054771 := by
  apply lucas_primality 101054771 (2 : ZMod 101054771)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (113, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (113, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) = 101054771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_37
      · exact prime_ninetyThreeCM_113
      · exact prime_ninetyThreeCM_2417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 101054771) ^ 50527385 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 101054771) ^ 20210954 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 101054771) ^ 2731210 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 101054771) ^ 894290 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 101054771) ^ 41810 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_109120091 : Nat.Prime 109120091 := by
  apply lucas_primality 109120091 (2 : ZMod 109120091)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10912009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10912009, 1)] : List FactorBlock).map factorBlockValue).prod) = 109120091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_10912009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 109120091) ^ 54560045 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 109120091) ^ 21824018 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 109120091) ^ 10 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_117231467 : Nat.Prime 117231467 := by
  apply lucas_primality 117231467 (2 : ZMod 117231467)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37, 1), (59, 1), (2441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37, 1), (59, 1), (2441, 1)] : List FactorBlock).map factorBlockValue).prod) = 117231467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_37
      · exact prime_ninetyThreeCM_59
      · exact prime_ninetyThreeCM_2441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 117231467) ^ 58615733 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 117231467) ^ 10657406 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 117231467) ^ 3168418 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 117231467) ^ 1986974 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 117231467) ^ 48026 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_117728189 : Nat.Prime 117728189 := by
  apply lucas_primality 117728189 (2 : ZMod 117728189)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29432047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29432047, 1)] : List FactorBlock).map factorBlockValue).prod) = 117728189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_29432047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 117728189) ^ 58864094 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 117728189) ^ 4 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_118249919 : Nat.Prime 118249919 := by
  apply lucas_primality 118249919 (7 : ZMod 118249919)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (439, 1), (134681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (439, 1), (134681, 1)] : List FactorBlock).map factorBlockValue).prod) = 118249919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_439
      · exact prime_ninetyThreeCM_134681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 118249919) ^ 59124959 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 118249919) ^ 269362 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 118249919) ^ 878 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_123196091 : Nat.Prime 123196091 := by
  apply lucas_primality 123196091 (2 : ZMod 123196091)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12319609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12319609, 1)] : List FactorBlock).map factorBlockValue).prod) = 123196091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_12319609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 123196091) ^ 61598045 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 123196091) ^ 24639218 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 123196091) ^ 10 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_129527533 : Nat.Prime 129527533 := by
  apply lucas_primality 129527533 (2 : ZMod 129527533)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1199329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1199329, 1)] : List FactorBlock).map factorBlockValue).prod) = 129527533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_1199329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 129527533) ^ 64763766 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 129527533) ^ 43175844 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 129527533) ^ 108 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_133948123 : Nat.Prime 133948123 := by
  apply lucas_primality 133948123 (3 : ZMod 133948123)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (383, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (383, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) = 133948123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_383
      · exact prime_ninetyThreeCM_757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 133948123) ^ 66974061 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 133948123) ^ 44649374 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 133948123) ^ 19135446 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 133948123) ^ 12177102 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 133948123) ^ 349734 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 133948123) ^ 176946 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_136685839 : Nat.Prime 136685839 := by
  apply lucas_primality 136685839 (3 : ZMod 136685839)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22780973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22780973, 1)] : List FactorBlock).map factorBlockValue).prod) = 136685839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_22780973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 136685839) ^ 68342919 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 136685839) ^ 45561946 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 136685839) ^ 6 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_140488433 : Nat.Prime 140488433 := by
  apply lucas_primality 140488433 (5 : ZMod 140488433)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (19, 1), (107, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (19, 1), (107, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 140488433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_107
      · exact prime_ninetyThreeCM_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 140488433) ^ 70244216 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140488433) ^ 20069776 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140488433) ^ 7394128 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140488433) ^ 1312976 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 140488433) ^ 227696 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_146642569 : Nat.Prime 146642569 := by
  apply lucas_primality 146642569 (11 : ZMod 146642569)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (149027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (149027, 1)] : List FactorBlock).map factorBlockValue).prod) = 146642569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_41
      · exact prime_ninetyThreeCM_149027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 146642569) ^ 73321284 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 146642569) ^ 48880856 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 146642569) ^ 3576648 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 146642569) ^ 984 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_164536159 : Nat.Prime 164536159 := by
  apply lucas_primality 164536159 (3 : ZMod 164536159)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (31, 1), (38461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (31, 1), (38461, 1)] : List FactorBlock).map factorBlockValue).prod) = 164536159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_23
      · exact prime_ninetyThreeCM_31
      · exact prime_ninetyThreeCM_38461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 164536159) ^ 82268079 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 164536159) ^ 54845386 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 164536159) ^ 7153746 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 164536159) ^ 5307618 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 164536159) ^ 4278 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_174666161 : Nat.Prime 174666161 := by
  apply lucas_primality 174666161 (7 : ZMod 174666161)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (17, 1), (128431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (17, 1), (128431, 1)] : List FactorBlock).map factorBlockValue).prod) = 174666161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_128431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 174666161) ^ 87333080 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 174666161) ^ 34933232 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 174666161) ^ 10274480 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 174666161) ^ 1360 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_190580743 : Nat.Prime 190580743 := by
  apply lucas_primality 190580743 (3 : ZMod 190580743)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (320843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (320843, 1)] : List FactorBlock).map factorBlockValue).prod) = 190580743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_320843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 190580743) ^ 95290371 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 190580743) ^ 63526914 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 190580743) ^ 17325522 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 190580743) ^ 594 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_197868361 : Nat.Prime 197868361 := by
  apply lucas_primality 197868361 (7 : ZMod 197868361)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (89, 1), (97, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (89, 1), (97, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 197868361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_89
      · exact prime_ninetyThreeCM_97
      · exact prime_ninetyThreeCM_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 197868361) ^ 98934180 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 197868361) ^ 65956120 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 197868361) ^ 39573672 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 197868361) ^ 2223240 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 197868361) ^ 2039880 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 197868361) ^ 1035960 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_202109543 : Nat.Prime 202109543 := by
  apply lucas_primality 202109543 (5 : ZMod 202109543)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101054771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101054771, 1)] : List FactorBlock).map factorBlockValue).prod) = 202109543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_101054771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 202109543) ^ 101054771 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 202109543) ^ 2 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_209121113 : Nat.Prime 209121113 := by
  apply lucas_primality 209121113 (3 : ZMod 209121113)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (26140139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (26140139, 1)] : List FactorBlock).map factorBlockValue).prod) = 209121113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_26140139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 209121113) ^ 104560556 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 209121113) ^ 8 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_211957771 : Nat.Prime 211957771 := by
  apply lucas_primality 211957771 (2 : ZMod 211957771)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (233, 1), (30323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (233, 1), (30323, 1)] : List FactorBlock).map factorBlockValue).prod) = 211957771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_233
      · exact prime_ninetyThreeCM_30323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 211957771) ^ 105978885 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 211957771) ^ 70652590 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 211957771) ^ 42391554 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 211957771) ^ 909690 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 211957771) ^ 6990 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_212513969 : Nat.Prime 212513969 := by
  apply lucas_primality 212513969 (3 : ZMod 212513969)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13282123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13282123, 1)] : List FactorBlock).map factorBlockValue).prod) = 212513969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_13282123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 212513969) ^ 106256984 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 212513969) ^ 16 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_227861197 : Nat.Prime 227861197 := by
  apply lucas_primality 227861197 (2 : ZMod 227861197)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (643, 1), (29531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (643, 1), (29531, 1)] : List FactorBlock).map factorBlockValue).prod) = 227861197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_643
      · exact prime_ninetyThreeCM_29531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 227861197) ^ 113930598 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 227861197) ^ 75953732 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 227861197) ^ 354372 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 227861197) ^ 7716 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_240361711 : Nat.Prime 240361711 := by
  apply lucas_primality 240361711 (13 : ZMod 240361711)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (8012057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (8012057, 1)] : List FactorBlock).map factorBlockValue).prod) = 240361711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_8012057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 240361711) ^ 120180855 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 240361711) ^ 80120570 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 240361711) ^ 48072342 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 240361711) ^ 30 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_241238287 : Nat.Prime 241238287 := by
  apply lucas_primality 241238287 (6 : ZMod 241238287)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (219707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (219707, 1)] : List FactorBlock).map factorBlockValue).prod) = 241238287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_61
      · exact prime_ninetyThreeCM_219707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 241238287) ^ 120619143 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 241238287) ^ 80412762 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 241238287) ^ 3954726 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 241238287) ^ 1098 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_243584909 : Nat.Prime 243584909 := by
  apply lucas_primality 243584909 (2 : ZMod 243584909)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (17, 1), (397, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (17, 1), (397, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod) = 243584909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_397
      · exact prime_ninetyThreeCM_1289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 243584909) ^ 121792454 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 243584909) ^ 34797844 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 243584909) ^ 14328524 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 243584909) ^ 613564 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 243584909) ^ 188972 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_251178359 : Nat.Prime 251178359 := by
  apply lucas_primality 251178359 (11 : ZMod 251178359)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (2058839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (2058839, 1)] : List FactorBlock).map factorBlockValue).prod) = 251178359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_61
      · exact prime_ninetyThreeCM_2058839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 251178359) ^ 125589179 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 251178359) ^ 4117678 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 251178359) ^ 122 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_255290261 : Nat.Prime 255290261 := by
  apply lucas_primality 255290261 (2 : ZMod 255290261)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (12764513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (12764513, 1)] : List FactorBlock).map factorBlockValue).prod) = 255290261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_12764513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 255290261) ^ 127645130 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 255290261) ^ 51058052 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 255290261) ^ 20 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_283061813 : Nat.Prime 283061813 := by
  apply lucas_primality 283061813 (2 : ZMod 283061813)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (727, 1), (8849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (727, 1), (8849, 1)] : List FactorBlock).map factorBlockValue).prod) = 283061813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_727
      · exact prime_ninetyThreeCM_8849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 283061813) ^ 141530906 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 283061813) ^ 25732892 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 283061813) ^ 389356 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 283061813) ^ 31988 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_288503729 : Nat.Prime 288503729 := by
  apply lucas_primality 288503729 (3 : ZMod 288503729)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (18031483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (18031483, 1)] : List FactorBlock).map factorBlockValue).prod) = 288503729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_18031483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 288503729) ^ 144251864 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 288503729) ^ 16 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_297503351 : Nat.Prime 297503351 := by
  apply lucas_primality 297503351 (13 : ZMod 297503351)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (5950067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (5950067, 1)] : List FactorBlock).map factorBlockValue).prod) = 297503351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_5950067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 297503351) ^ 148751675 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 297503351) ^ 59500670 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 297503351) ^ 50 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_317540261 : Nat.Prime 317540261 := by
  apply lucas_primality 317540261 (2 : ZMod 317540261)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (15877013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (15877013, 1)] : List FactorBlock).map factorBlockValue).prod) = 317540261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_15877013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 317540261) ^ 158770130 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 317540261) ^ 63508052 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 317540261) ^ 20 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_329511769 : Nat.Prime 329511769 := by
  apply lucas_primality 329511769 (7 : ZMod 329511769)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2543, 1), (5399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2543, 1), (5399, 1)] : List FactorBlock).map factorBlockValue).prod) = 329511769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_2543
      · exact prime_ninetyThreeCM_5399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 329511769) ^ 164755884 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 329511769) ^ 109837256 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 329511769) ^ 129576 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 329511769) ^ 61032 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_349332323 : Nat.Prime 349332323 := by
  apply lucas_primality 349332323 (2 : ZMod 349332323)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (174666161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (174666161, 1)] : List FactorBlock).map factorBlockValue).prod) = 349332323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_174666161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 349332323) ^ 174666161 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 349332323) ^ 2 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_350039663 : Nat.Prime 350039663 := by
  apply lucas_primality 350039663 (5 : ZMod 350039663)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (806543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (806543, 1)] : List FactorBlock).map factorBlockValue).prod) = 350039663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_31
      · exact prime_ninetyThreeCM_806543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 350039663) ^ 175019831 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 350039663) ^ 50005666 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 350039663) ^ 11291602 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 350039663) ^ 434 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_372229681 : Nat.Prime 372229681 := by
  apply lucas_primality 372229681 (13 : ZMod 372229681)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (311, 1), (4987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (311, 1), (4987, 1)] : List FactorBlock).map factorBlockValue).prod) = 372229681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_311
      · exact prime_ninetyThreeCM_4987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 372229681) ^ 186114840 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 372229681) ^ 124076560 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 372229681) ^ 74445936 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 372229681) ^ 1196880 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 372229681) ^ 74640 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_376759751 : Nat.Prime 376759751 := by
  apply lucas_primality 376759751 (7 : ZMod 376759751)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (1507039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (1507039, 1)] : List FactorBlock).map factorBlockValue).prod) = 376759751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_1507039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 376759751) ^ 188379875 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 376759751) ^ 75351950 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 376759751) ^ 250 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_419640443 : Nat.Prime 419640443 := by
  apply lucas_primality 419640443 (2 : ZMod 419640443)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (16140017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (16140017, 1)] : List FactorBlock).map factorBlockValue).prod) = 419640443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_16140017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 419640443) ^ 209820221 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 419640443) ^ 32280034 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 419640443) ^ 26 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_424874449 : Nat.Prime 424874449 := by
  apply lucas_primality 424874449 (7 : ZMod 424874449)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (2950517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (2950517, 1)] : List FactorBlock).map factorBlockValue).prod) = 424874449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_2950517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 424874449) ^ 212437224 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 424874449) ^ 141624816 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 424874449) ^ 144 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_426790687 : Nat.Prime 426790687 := by
  apply lucas_primality 426790687 (6 : ZMod 426790687)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (107, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (107, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod) = 426790687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_107
      · exact prime_ninetyThreeCM_13567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 426790687) ^ 213395343 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 426790687) ^ 142263562 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 426790687) ^ 60970098 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 426790687) ^ 3988698 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 426790687) ^ 31458 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_451346177 : Nat.Prime 451346177 := by
  apply lucas_primality 451346177 (3 : ZMod 451346177)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (229, 1), (7699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (229, 1), (7699, 1)] : List FactorBlock).map factorBlockValue).prod) = 451346177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_229
      · exact prime_ninetyThreeCM_7699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 451346177) ^ 225673088 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 451346177) ^ 1970944 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 451346177) ^ 58624 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_453134273 : Nat.Prime 453134273 := by
  apply lucas_primality 453134273 (3 : ZMod 453134273)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (263, 1), (26921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (263, 1), (26921, 1)] : List FactorBlock).map factorBlockValue).prod) = 453134273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_263
      · exact prime_ninetyThreeCM_26921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 453134273) ^ 226567136 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 453134273) ^ 1722944 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 453134273) ^ 16832 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_502356719 : Nat.Prime 502356719 := by
  apply lucas_primality 502356719 (7 : ZMod 502356719)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (251178359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (251178359, 1)] : List FactorBlock).map factorBlockValue).prod) = 502356719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_251178359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 502356719) ^ 251178359 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 502356719) ^ 2 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_506471549 : Nat.Prime 506471549 := by
  apply lucas_primality 506471549 (2 : ZMod 506471549)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (17, 1), (431, 1), (1571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (17, 1), (431, 1), (1571, 1)] : List FactorBlock).map factorBlockValue).prod) = 506471549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_431
      · exact prime_ninetyThreeCM_1571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 506471549) ^ 253235774 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 506471549) ^ 46042868 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 506471549) ^ 29792444 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 506471549) ^ 1175108 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 506471549) ^ 322388 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_510580523 : Nat.Prime 510580523 := by
  apply lucas_primality 510580523 (2 : ZMod 510580523)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (255290261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (255290261, 1)] : List FactorBlock).map factorBlockValue).prod) = 510580523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_255290261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 510580523) ^ 255290261 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 510580523) ^ 2 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_512837467 : Nat.Prime 512837467 := by
  apply lucas_primality 512837467 (2 : ZMod 512837467)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1831, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1831, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod) = 512837467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_1831
      · exact prime_ninetyThreeCM_46681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 512837467) ^ 256418733 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 512837467) ^ 170945822 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 512837467) ^ 280086 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 512837467) ^ 10986 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_525908729 : Nat.Prime 525908729 := by
  apply lucas_primality 525908729 (3 : ZMod 525908729)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (981173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (981173, 1)] : List FactorBlock).map factorBlockValue).prod) = 525908729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_67
      · exact prime_ninetyThreeCM_981173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 525908729) ^ 262954364 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 525908729) ^ 7849384 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 525908729) ^ 536 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_539857273 : Nat.Prime 539857273 := by
  apply lucas_primality 539857273 (11 : ZMod 539857273)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (233, 1), (3329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (233, 1), (3329, 1)] : List FactorBlock).map factorBlockValue).prod) = 539857273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_233
      · exact prime_ninetyThreeCM_3329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 539857273) ^ 269928636 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 539857273) ^ 179952424 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 539857273) ^ 18615768 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 539857273) ^ 2316984 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 539857273) ^ 162168 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_601350907 : Nat.Prime 601350907 := by
  apply lucas_primality 601350907 (3 : ZMod 601350907)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (2099, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (2099, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) = 601350907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_2099
      · exact prime_ninetyThreeCM_3673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 601350907) ^ 300675453 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 601350907) ^ 200450302 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 601350907) ^ 46257762 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 601350907) ^ 286494 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 601350907) ^ 163722 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_611166821 : Nat.Prime 611166821 := by
  apply lucas_primality 611166821 (3 : ZMod 611166821)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (971, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (971, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) = 611166821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_971
      · exact prime_ninetyThreeCM_2861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 611166821) ^ 305583410 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 611166821) ^ 122233364 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 611166821) ^ 55560620 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 611166821) ^ 629420 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 611166821) ^ 213620 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_625022623 : Nat.Prime 625022623 := by
  apply lucas_primality 625022623 (5 : ZMod 625022623)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (1653499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (1653499, 1)] : List FactorBlock).map factorBlockValue).prod) = 625022623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_1653499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 625022623) ^ 312511311 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 625022623) ^ 208340874 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 625022623) ^ 89288946 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 625022623) ^ 378 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_632431889 : Nat.Prime 632431889 := by
  apply lucas_primality 632431889 (3 : ZMod 632431889)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (41, 1), (87643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (41, 1), (87643, 1)] : List FactorBlock).map factorBlockValue).prod) = 632431889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_41
      · exact prime_ninetyThreeCM_87643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 632431889) ^ 316215944 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 632431889) ^ 57493808 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 632431889) ^ 15425168 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 632431889) ^ 7216 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_660160573 : Nat.Prime 660160573 := by
  apply lucas_primality 660160573 (11 : ZMod 660160573)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (55013381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (55013381, 1)] : List FactorBlock).map factorBlockValue).prod) = 660160573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_55013381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 660160573) ^ 330080286 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 660160573) ^ 220053524 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 660160573) ^ 12 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_679626917 : Nat.Prime 679626917 := by
  apply lucas_primality 679626917 (2 : ZMod 679626917)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (313, 1), (647, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (313, 1), (647, 1), (839, 1)] : List FactorBlock).map factorBlockValue).prod) = 679626917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_313
      · exact prime_ninetyThreeCM_647
      · exact prime_ninetyThreeCM_839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 679626917) ^ 339813458 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 679626917) ^ 2171332 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 679626917) ^ 1050428 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 679626917) ^ 810044 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_710531981 : Nat.Prime 710531981 := by
  apply lucas_primality 710531981 (2 : ZMod 710531981)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (127, 1), (14723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (127, 1), (14723, 1)] : List FactorBlock).map factorBlockValue).prod) = 710531981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_127
      · exact prime_ninetyThreeCM_14723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 710531981) ^ 355265990 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 710531981) ^ 142106396 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 710531981) ^ 37396420 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 710531981) ^ 5594740 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 710531981) ^ 48260 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_718218871 : Nat.Prime 718218871 := by
  apply lucas_primality 718218871 (3 : ZMod 718218871)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (673, 1), (35573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (673, 1), (35573, 1)] : List FactorBlock).map factorBlockValue).prod) = 718218871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_673
      · exact prime_ninetyThreeCM_35573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 718218871) ^ 359109435 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 718218871) ^ 239406290 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 718218871) ^ 143643774 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 718218871) ^ 1067190 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 718218871) ^ 20190 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_821877541 : Nat.Prime 821877541 := by
  apply lucas_primality 821877541 (2 : ZMod 821877541)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (71, 1), (17539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (71, 1), (17539, 1)] : List FactorBlock).map factorBlockValue).prod) = 821877541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_71
      · exact prime_ninetyThreeCM_17539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 821877541) ^ 410938770 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 821877541) ^ 273959180 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 821877541) ^ 164375508 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 821877541) ^ 74716140 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 821877541) ^ 11575740 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 821877541) ^ 46860 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_883658227 : Nat.Prime 883658227 := by
  apply lucas_primality 883658227 (2 : ZMod 883658227)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13388761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13388761, 1)] : List FactorBlock).map factorBlockValue).prod) = 883658227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_13388761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 883658227) ^ 441829113 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 883658227) ^ 294552742 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 883658227) ^ 80332566 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 883658227) ^ 66 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1022753587 : Nat.Prime 1022753587 := by
  apply lucas_primality 1022753587 (2 : ZMod 1022753587)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1091, 1), (156241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1091, 1), (156241, 1)] : List FactorBlock).map factorBlockValue).prod) = 1022753587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_1091
      · exact prime_ninetyThreeCM_156241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1022753587) ^ 511376793 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022753587) ^ 340917862 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022753587) ^ 937446 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1022753587) ^ 6546 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1226128357 : Nat.Prime 1226128357 := by
  apply lucas_primality 1226128357 (2 : ZMod 1226128357)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (109, 1), (312469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (109, 1), (312469, 1)] : List FactorBlock).map factorBlockValue).prod) = 1226128357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_109
      · exact prime_ninetyThreeCM_312469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1226128357) ^ 613064178 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1226128357) ^ 408709452 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1226128357) ^ 11248884 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1226128357) ^ 3924 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1264863779 : Nat.Prime 1264863779 := by
  apply lucas_primality 1264863779 (2 : ZMod 1264863779)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (632431889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (632431889, 1)] : List FactorBlock).map factorBlockValue).prod) = 1264863779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_632431889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1264863779) ^ 632431889 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1264863779) ^ 2 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1283013857 : Nat.Prime 1283013857 := by
  apply lucas_primality 1283013857 (3 : ZMod 1283013857)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (40094183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (40094183, 1)] : List FactorBlock).map factorBlockValue).prod) = 1283013857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_40094183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1283013857) ^ 641506928 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1283013857) ^ 32 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1326111953 : Nat.Prime 1326111953 := by
  apply lucas_primality 1326111953 (3 : ZMod 1326111953)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (113, 1), (131, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (113, 1), (131, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1326111953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_113
      · exact prime_ninetyThreeCM_131
      · exact prime_ninetyThreeCM_509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1326111953) ^ 663055976 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1326111953) ^ 120555632 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1326111953) ^ 11735504 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1326111953) ^ 10122992 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1326111953) ^ 2605328 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1394573611 : Nat.Prime 1394573611 := by
  apply lucas_primality 1394573611 (3 : ZMod 1394573611)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (193, 1), (240859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (193, 1), (240859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1394573611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_193
      · exact prime_ninetyThreeCM_240859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1394573611) ^ 697286805 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1394573611) ^ 464857870 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1394573611) ^ 278914722 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1394573611) ^ 7225770 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1394573611) ^ 5790 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1530995519 : Nat.Prime 1530995519 := by
  apply lucas_primality 1530995519 (7 : ZMod 1530995519)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (58884443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (58884443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1530995519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_58884443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1530995519) ^ 765497759 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1530995519) ^ 117768886 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 1530995519) ^ 26 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1962562709 : Nat.Prime 1962562709 := by
  apply lucas_primality 1962562709 (2 : ZMod 1962562709)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1291, 1), (380047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1291, 1), (380047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1962562709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_1291
      · exact prime_ninetyThreeCM_380047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1962562709) ^ 981281354 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1962562709) ^ 1520188 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1962562709) ^ 5164 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2103987293 : Nat.Prime 2103987293 := by
  apply lucas_primality 2103987293 (2 : ZMod 2103987293)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (293, 2), (557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (293, 2), (557, 1)] : List FactorBlock).map factorBlockValue).prod) = 2103987293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_293
      · exact prime_ninetyThreeCM_557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2103987293) ^ 1051993646 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2103987293) ^ 191271572 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2103987293) ^ 7180844 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2103987293) ^ 3777356 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2119577711 : Nat.Prime 2119577711 := by
  apply lucas_primality 2119577711 (11 : ZMod 2119577711)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (211957771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (211957771, 1)] : List FactorBlock).map factorBlockValue).prod) = 2119577711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_211957771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 2119577711) ^ 1059788855 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 2119577711) ^ 423915542 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 2119577711) ^ 10 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2179272803 : Nat.Prime 2179272803 := by
  apply lucas_primality 2179272803 (2 : ZMod 2179272803)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (5367667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (5367667, 1)] : List FactorBlock).map factorBlockValue).prod) = 2179272803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_5367667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2179272803) ^ 1089636401 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2179272803) ^ 311324686 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2179272803) ^ 75147338 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2179272803) ^ 406 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2215580651 : Nat.Prime 2215580651 := by
  apply lucas_primality 2215580651 (2 : ZMod 2215580651)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (167, 1), (265339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (167, 1), (265339, 1)] : List FactorBlock).map factorBlockValue).prod) = 2215580651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_167
      · exact prime_ninetyThreeCM_265339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2215580651) ^ 1107790325 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2215580651) ^ 443116130 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2215580651) ^ 13266950 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 2215580651) ^ 8350 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2799144431 : Nat.Prime 2799144431 := by
  apply lucas_primality 2799144431 (23 : ZMod 2799144431)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1069, 1), (261847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1069, 1), (261847, 1)] : List FactorBlock).map factorBlockValue).prod) = 2799144431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_1069
      · exact prime_ninetyThreeCM_261847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 2799144431) ^ 1399572215 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (23 : ZMod 2799144431) ^ 559828886 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (23 : ZMod 2799144431) ^ 2618470 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (23 : ZMod 2799144431) ^ 10690 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_3032991791 : Nat.Prime 3032991791 := by
  apply lucas_primality 3032991791 (7 : ZMod 3032991791)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6089, 1), (49811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6089, 1), (49811, 1)] : List FactorBlock).map factorBlockValue).prod) = 3032991791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_6089
      · exact prime_ninetyThreeCM_49811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3032991791) ^ 1516495895 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3032991791) ^ 606598358 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3032991791) ^ 498110 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 3032991791) ^ 60890 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_3158235109 : Nat.Prime 3158235109 := by
  apply lucas_primality 3158235109 (6 : ZMod 3158235109)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (1619, 1), (7741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (1619, 1), (7741, 1)] : List FactorBlock).map factorBlockValue).prod) = 3158235109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_1619
      · exact prime_ninetyThreeCM_7741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3158235109) ^ 1579117554 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3158235109) ^ 1052745036 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3158235109) ^ 451176444 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3158235109) ^ 1950732 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 3158235109) ^ 407988 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_3299952581 : Nat.Prime 3299952581 := by
  apply lucas_primality 3299952581 (3 : ZMod 3299952581)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (311, 1), (530539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (311, 1), (530539, 1)] : List FactorBlock).map factorBlockValue).prod) = 3299952581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_311
      · exact prime_ninetyThreeCM_530539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3299952581) ^ 1649976290 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3299952581) ^ 659990516 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3299952581) ^ 10610780 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3299952581) ^ 6220 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_3375092009 : Nat.Prime 3375092009 := by
  apply lucas_primality 3375092009 (3 : ZMod 3375092009)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (2357, 1), (10529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (2357, 1), (10529, 1)] : List FactorBlock).map factorBlockValue).prod) = 3375092009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_2357
      · exact prime_ninetyThreeCM_10529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3375092009) ^ 1687546004 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3375092009) ^ 198534824 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3375092009) ^ 1431944 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 3375092009) ^ 320552 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_4988360717 : Nat.Prime 4988360717 := by
  apply lucas_primality 4988360717 (2 : ZMod 4988360717)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (197, 1), (6330407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (197, 1), (6330407, 1)] : List FactorBlock).map factorBlockValue).prod) = 4988360717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_197
      · exact prime_ninetyThreeCM_6330407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4988360717) ^ 2494180358 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4988360717) ^ 25321628 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4988360717) ^ 788 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_5156451233 : Nat.Prime 5156451233 := by
  apply lucas_primality 5156451233 (3 : ZMod 5156451233)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (631, 1), (255371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (631, 1), (255371, 1)] : List FactorBlock).map factorBlockValue).prod) = 5156451233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_631
      · exact prime_ninetyThreeCM_255371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5156451233) ^ 2578225616 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5156451233) ^ 8171872 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5156451233) ^ 20192 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_5219532119 : Nat.Prime 5219532119 := by
  apply lucas_primality 5219532119 (7 : ZMod 5219532119)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (24390337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (24390337, 1)] : List FactorBlock).map factorBlockValue).prod) = 5219532119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_107
      · exact prime_ninetyThreeCM_24390337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 5219532119) ^ 2609766059 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 5219532119) ^ 48780674 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 5219532119) ^ 214 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_5656385737 : Nat.Prime 5656385737 := by
  apply lucas_primality 5656385737 (11 : ZMod 5656385737)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (29, 1), (31, 1), (29129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (29, 1), (31, 1), (29129, 1)] : List FactorBlock).map factorBlockValue).prod) = 5656385737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_31
      · exact prime_ninetyThreeCM_29129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5656385737) ^ 2828192868 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 5656385737) ^ 1885461912 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 5656385737) ^ 195047784 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 5656385737) ^ 182464056 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 5656385737) ^ 194184 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_6064011181 : Nat.Prime 6064011181 := by
  apply lucas_primality 6064011181 (2 : ZMod 6064011181)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (23, 1), (86161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (23, 1), (86161, 1)] : List FactorBlock).map factorBlockValue).prod) = 6064011181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_23
      · exact prime_ninetyThreeCM_86161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6064011181) ^ 3032005590 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6064011181) ^ 2021337060 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6064011181) ^ 1212802236 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6064011181) ^ 356706540 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6064011181) ^ 263652660 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6064011181) ^ 70380 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_6264808603 : Nat.Prime 6264808603 := by
  apply lucas_primality 6264808603 (2 : ZMod 6264808603)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (67, 1), (379, 1), (3163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (67, 1), (379, 1), (3163, 1)] : List FactorBlock).map factorBlockValue).prod) = 6264808603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_67
      · exact prime_ninetyThreeCM_379
      · exact prime_ninetyThreeCM_3163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6264808603) ^ 3132404301 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6264808603) ^ 2088269534 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6264808603) ^ 481908354 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6264808603) ^ 93504606 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6264808603) ^ 16529838 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6264808603) ^ 1980654 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_7065358357 : Nat.Prime 7065358357 := by
  apply lucas_primality 7065358357 (2 : ZMod 7065358357)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (84111409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (84111409, 1)] : List FactorBlock).map factorBlockValue).prod) = 7065358357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_84111409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7065358357) ^ 3532679178 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7065358357) ^ 2355119452 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7065358357) ^ 1009336908 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7065358357) ^ 84 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_7100779711 : Nat.Prime 7100779711 := by
  apply lucas_primality 7100779711 (3 : ZMod 7100779711)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (647, 1), (11801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (647, 1), (11801, 1)] : List FactorBlock).map factorBlockValue).prod) = 7100779711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_31
      · exact prime_ninetyThreeCM_647
      · exact prime_ninetyThreeCM_11801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7100779711) ^ 3550389855 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7100779711) ^ 2366926570 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7100779711) ^ 1420155942 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7100779711) ^ 229057410 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7100779711) ^ 10974930 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7100779711) ^ 601710 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_7101960143 : Nat.Prime 7101960143 := by
  apply lucas_primality 7101960143 (5 : ZMod 7101960143)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (27960473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (27960473, 1)] : List FactorBlock).map factorBlockValue).prod) = 7101960143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_127
      · exact prime_ninetyThreeCM_27960473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7101960143) ^ 3550980071 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 7101960143) ^ 55920946 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 7101960143) ^ 254 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_9614605003 : Nat.Prime 9614605003 := by
  apply lucas_primality 9614605003 (3 : ZMod 9614605003)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (199, 1), (8052433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (199, 1), (8052433, 1)] : List FactorBlock).map factorBlockValue).prod) = 9614605003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_199
      · exact prime_ninetyThreeCM_8052433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9614605003) ^ 4807302501 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9614605003) ^ 3204868334 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9614605003) ^ 48314598 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9614605003) ^ 1194 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_11032056107 : Nat.Prime 11032056107 := by
  apply lucas_primality 11032056107 (2 : ZMod 11032056107)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (53, 1), (2214383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (53, 1), (2214383, 1)] : List FactorBlock).map factorBlockValue).prod) = 11032056107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_47
      · exact prime_ninetyThreeCM_53
      · exact prime_ninetyThreeCM_2214383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11032056107) ^ 5516028053 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11032056107) ^ 234724598 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11032056107) ^ 208152002 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 11032056107) ^ 4982 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_13355729521 : Nat.Prime 13355729521 := by
  apply lucas_primality 13355729521 (11 : ZMod 13355729521)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (7949839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (7949839, 1)] : List FactorBlock).map factorBlockValue).prod) = 13355729521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_7949839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 13355729521) ^ 6677864760 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 13355729521) ^ 4451909840 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 13355729521) ^ 2671145904 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 13355729521) ^ 1907961360 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 13355729521) ^ 1680 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_13414239347 : Nat.Prime 13414239347 := by
  apply lucas_primality 13414239347 (2 : ZMod 13414239347)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (24733, 1), (271181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (24733, 1), (271181, 1)] : List FactorBlock).map factorBlockValue).prod) = 13414239347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_24733
      · exact prime_ninetyThreeCM_271181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13414239347) ^ 6707119673 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13414239347) ^ 542362 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13414239347) ^ 49466 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_13488857407 : Nat.Prime 13488857407 := by
  apply lucas_primality 13488857407 (3 : ZMod 13488857407)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (25840723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (25840723, 1)] : List FactorBlock).map factorBlockValue).prod) = 13488857407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_25840723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13488857407) ^ 6744428703 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13488857407) ^ 4496285802 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13488857407) ^ 465133014 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 13488857407) ^ 522 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_15361318597 : Nat.Prime 15361318597 := by
  apply lucas_primality 15361318597 (2 : ZMod 15361318597)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (6131, 1), (16061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (6131, 1), (16061, 1)] : List FactorBlock).map factorBlockValue).prod) = 15361318597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_6131
      · exact prime_ninetyThreeCM_16061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15361318597) ^ 7680659298 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15361318597) ^ 5120439532 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15361318597) ^ 1181639892 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15361318597) ^ 2505516 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15361318597) ^ 956436 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_15905848087 : Nat.Prime 15905848087 := by
  apply lucas_primality 15905848087 (5 : ZMod 15905848087)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (883658227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (883658227, 1)] : List FactorBlock).map factorBlockValue).prod) = 15905848087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_883658227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15905848087) ^ 7952924043 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 15905848087) ^ 5301949362 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 15905848087) ^ 18 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_16482262193 : Nat.Prime 16482262193 := by
  apply lucas_primality 16482262193 (5 : ZMod 16482262193)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (93649217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (93649217, 1)] : List FactorBlock).map factorBlockValue).prod) = 16482262193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_93649217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 16482262193) ^ 8241131096 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 16482262193) ^ 1498387472 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 16482262193) ^ 176 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_20800054549 : Nat.Prime 20800054549 := by
  apply lucas_primality 20800054549 (6 : ZMod 20800054549)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (13, 1), (6349223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (13, 1), (6349223, 1)] : List FactorBlock).map factorBlockValue).prod) = 20800054549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_6349223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 20800054549) ^ 10400027274 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 20800054549) ^ 6933351516 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 20800054549) ^ 2971436364 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 20800054549) ^ 1600004196 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 20800054549) ^ 3276 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_21952703239 : Nat.Prime 21952703239 := by
  apply lucas_primality 21952703239 (3 : ZMod 21952703239)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (683, 1), (1187, 1), (4513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (683, 1), (1187, 1), (4513, 1)] : List FactorBlock).map factorBlockValue).prod) = 21952703239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_683
      · exact prime_ninetyThreeCM_1187
      · exact prime_ninetyThreeCM_4513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21952703239) ^ 10976351619 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21952703239) ^ 7317567746 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21952703239) ^ 32141586 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21952703239) ^ 18494274 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21952703239) ^ 4864326 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_22320483049 : Nat.Prime 22320483049 := by
  apply lucas_primality 22320483049 (11 : ZMod 22320483049)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (59, 1), (5254351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (59, 1), (5254351, 1)] : List FactorBlock).map factorBlockValue).prod) = 22320483049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_59
      · exact prime_ninetyThreeCM_5254351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 22320483049) ^ 11160241524 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 22320483049) ^ 7440161016 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 22320483049) ^ 378313272 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 22320483049) ^ 4248 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_25924159453 : Nat.Prime 25924159453 := by
  apply lucas_primality 25924159453 (2 : ZMod 25924159453)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (41, 1), (53, 1), (58481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (41, 1), (53, 1), (58481, 1)] : List FactorBlock).map factorBlockValue).prod) = 25924159453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_41
      · exact prime_ninetyThreeCM_53
      · exact prime_ninetyThreeCM_58481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25924159453) ^ 12962079726 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 25924159453) ^ 8641386484 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 25924159453) ^ 1524950556 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 25924159453) ^ 632296572 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 25924159453) ^ 489135084 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 25924159453) ^ 443292 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_26399620649 : Nat.Prime 26399620649 := by
  apply lucas_primality 26399620649 (3 : ZMod 26399620649)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3299952581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3299952581, 1)] : List FactorBlock).map factorBlockValue).prod) = 26399620649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3299952581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 26399620649) ^ 13199810324 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 26399620649) ^ 8 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_27475877927 : Nat.Prime 27475877927 := by
  apply lucas_primality 27475877927 (5 : ZMod 27475877927)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1962562709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1962562709, 1)] : List FactorBlock).map factorBlockValue).prod) = 27475877927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_1962562709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 27475877927) ^ 13737938963 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 27475877927) ^ 3925125418 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 27475877927) ^ 14 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_27924635539 : Nat.Prime 27924635539 := by
  apply lucas_primality 27924635539 (2 : ZMod 27924635539)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (347, 1), (4470803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (347, 1), (4470803, 1)] : List FactorBlock).map factorBlockValue).prod) = 27924635539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_347
      · exact prime_ninetyThreeCM_4470803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27924635539) ^ 13962317769 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 27924635539) ^ 9308211846 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 27924635539) ^ 80474454 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 27924635539) ^ 6246 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_38724633553 : Nat.Prime 38724633553 := by
  apply lucas_primality 38724633553 (5 : ZMod 38724633553)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (19, 1), (233, 1), (16567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (19, 1), (233, 1), (16567, 1)] : List FactorBlock).map factorBlockValue).prod) = 38724633553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_233
      · exact prime_ninetyThreeCM_16567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38724633553) ^ 19362316776 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38724633553) ^ 12908211184 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38724633553) ^ 3520421232 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38724633553) ^ 2038138608 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38724633553) ^ 166200144 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 38724633553) ^ 2337456 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_41947948517 : Nat.Prime 41947948517 := by
  apply lucas_primality 41947948517 (2 : ZMod 41947948517)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (1187, 1), (464993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (1187, 1), (464993, 1)] : List FactorBlock).map factorBlockValue).prod) = 41947948517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_1187
      · exact prime_ninetyThreeCM_464993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41947948517) ^ 20973974258 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 41947948517) ^ 2207786764 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 41947948517) ^ 35339468 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 41947948517) ^ 90212 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_43014390583 : Nat.Prime 43014390583 := by
  apply lucas_primality 43014390583 (3 : ZMod 43014390583)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (179, 1), (677, 1), (59159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (179, 1), (677, 1), (59159, 1)] : List FactorBlock).map factorBlockValue).prod) = 43014390583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_179
      · exact prime_ninetyThreeCM_677
      · exact prime_ninetyThreeCM_59159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 43014390583) ^ 21507195291 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 43014390583) ^ 14338130194 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 43014390583) ^ 240303858 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 43014390583) ^ 63536766 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 43014390583) ^ 727098 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_48288974869 : Nat.Prime 48288974869 := by
  apply lucas_primality 48288974869 (2 : ZMod 48288974869)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (853, 1), (1572521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (853, 1), (1572521, 1)] : List FactorBlock).map factorBlockValue).prod) = 48288974869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_853
      · exact prime_ninetyThreeCM_1572521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48288974869) ^ 24144487434 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 48288974869) ^ 16096324956 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 48288974869) ^ 56610756 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 48288974869) ^ 30708 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_76600515707 : Nat.Prime 76600515707 := by
  apply lucas_primality 76600515707 (2 : ZMod 76600515707)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (43, 1), (719, 1), (8663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (43, 1), (719, 1), (8663, 1)] : List FactorBlock).map factorBlockValue).prod) = 76600515707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_43
      · exact prime_ninetyThreeCM_719
      · exact prime_ninetyThreeCM_8663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76600515707) ^ 38300257853 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76600515707) ^ 6963683246 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76600515707) ^ 5892347362 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76600515707) ^ 1781407342 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76600515707) ^ 106537574 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 76600515707) ^ 8842262 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_77661067049 : Nat.Prime 77661067049 := by
  apply lucas_primality 77661067049 (3 : ZMod 77661067049)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (164536159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (164536159, 1)] : List FactorBlock).map factorBlockValue).prod) = 77661067049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_59
      · exact prime_ninetyThreeCM_164536159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 77661067049) ^ 38830533524 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 77661067049) ^ 1316289272 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 77661067049) ^ 472 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_83545257253 : Nat.Prime 83545257253 := by
  apply lucas_primality 83545257253 (2 : ZMod 83545257253)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (137, 1), (50818283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (137, 1), (50818283, 1)] : List FactorBlock).map factorBlockValue).prod) = 83545257253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_137
      · exact prime_ninetyThreeCM_50818283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83545257253) ^ 41772628626 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83545257253) ^ 27848419084 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83545257253) ^ 609819396 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83545257253) ^ 1644 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_109001079469 : Nat.Prime 109001079469 := by
  apply lucas_primality 109001079469 (6 : ZMod 109001079469)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (2939, 1), (60601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (2939, 1), (60601, 1)] : List FactorBlock).map factorBlockValue).prod) = 109001079469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_2939
      · exact prime_ninetyThreeCM_60601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 109001079469) ^ 54500539734 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 109001079469) ^ 36333693156 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 109001079469) ^ 6411828204 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 109001079469) ^ 37087812 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 109001079469) ^ 1798668 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_180560403181 : Nat.Prime 180560403181 := by
  apply lucas_primality 180560403181 (6 : ZMod 180560403181)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (53, 1), (1307, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (53, 1), (1307, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) = 180560403181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_53
      · exact prime_ninetyThreeCM_1307
      · exact prime_ninetyThreeCM_1609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 180560403181) ^ 90280201590 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 180560403181) ^ 60186801060 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 180560403181) ^ 36112080636 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 180560403181) ^ 3406800060 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 180560403181) ^ 138148740 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 180560403181) ^ 112219020 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_181365540121 : Nat.Prime 181365540121 := by
  apply lucas_primality 181365540121 (7 : ZMod 181365540121)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (67, 1), (1907, 1), (3943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (67, 1), (1907, 1), (3943, 1)] : List FactorBlock).map factorBlockValue).prod) = 181365540121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_67
      · exact prime_ninetyThreeCM_1907
      · exact prime_ninetyThreeCM_3943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 181365540121) ^ 90682770060 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 181365540121) ^ 60455180040 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 181365540121) ^ 36273108024 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 181365540121) ^ 2706948360 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 181365540121) ^ 95105160 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 181365540121) ^ 45996840 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_229506256613 : Nat.Prime 229506256613 := by
  apply lucas_primality 229506256613 (2 : ZMod 229506256613)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (3375092009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (3375092009, 1)] : List FactorBlock).map factorBlockValue).prod) = 229506256613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_3375092009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 229506256613) ^ 114753128306 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 229506256613) ^ 13500368036 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 229506256613) ^ 68 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_276643521857 : Nat.Prime 276643521857 := by
  apply lucas_primality 276643521857 (3 : ZMod 276643521857)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (31, 1), (10725943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (31, 1), (10725943, 1)] : List FactorBlock).map factorBlockValue).prod) = 276643521857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_31
      · exact prime_ninetyThreeCM_10725943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 276643521857) ^ 138321760928 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 276643521857) ^ 21280270912 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 276643521857) ^ 8923984576 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 276643521857) ^ 25792 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_289907649791 : Nat.Prime 289907649791 := by
  apply lucas_primality 289907649791 (7 : ZMod 289907649791)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (29, 1), (523, 1), (15797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (29, 1), (523, 1), (15797, 1)] : List FactorBlock).map factorBlockValue).prod) = 289907649791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_523
      · exact prime_ninetyThreeCM_15797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 289907649791) ^ 144953824895 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 289907649791) ^ 57981529958 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 289907649791) ^ 26355240890 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 289907649791) ^ 9996815510 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 289907649791) ^ 554316730 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 289907649791) ^ 18352070 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_298544622377 : Nat.Prime 298544622377 := by
  apply lucas_primality 298544622377 (3 : ZMod 298544622377)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (13, 1), (37280797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (13, 1), (37280797, 1)] : List FactorBlock).map factorBlockValue).prod) = 298544622377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_37280797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 298544622377) ^ 149272311188 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 298544622377) ^ 42649231768 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 298544622377) ^ 27140420216 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 298544622377) ^ 22964970952 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 298544622377) ^ 8008 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_338623015513 : Nat.Prime 338623015513 := by
  apply lucas_primality 338623015513 (5 : ZMod 338623015513)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (149, 1), (94693237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (149, 1), (94693237, 1)] : List FactorBlock).map factorBlockValue).prod) = 338623015513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_149
      · exact prime_ninetyThreeCM_94693237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 338623015513) ^ 169311507756 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 338623015513) ^ 112874338504 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 338623015513) ^ 2272637688 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 338623015513) ^ 3576 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_459224326553 : Nat.Prime 459224326553 := by
  apply lucas_primality 459224326553 (3 : ZMod 459224326553)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (107, 1), (5413, 1), (99109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (107, 1), (5413, 1), (99109, 1)] : List FactorBlock).map factorBlockValue).prod) = 459224326553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_107
      · exact prime_ninetyThreeCM_5413
      · exact prime_ninetyThreeCM_99109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 459224326553) ^ 229612163276 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 459224326553) ^ 4291816136 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 459224326553) ^ 84837304 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 459224326553) ^ 4633528 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_554824139297 : Nat.Prime 554824139297 := by
  apply lucas_primality 554824139297 (3 : ZMod 554824139297)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (37, 1), (66943067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (37, 1), (66943067, 1)] : List FactorBlock).map factorBlockValue).prod) = 554824139297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_37
      · exact prime_ninetyThreeCM_66943067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 554824139297) ^ 277412069648 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 554824139297) ^ 79260591328 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 554824139297) ^ 14995247008 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 554824139297) ^ 8288 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_596882146717 : Nat.Prime 596882146717 := by
  apply lucas_primality 596882146717 (2 : ZMod 596882146717)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (673, 1), (3659, 1), (6733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (673, 1), (3659, 1), (6733, 1)] : List FactorBlock).map factorBlockValue).prod) = 596882146717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_673
      · exact prime_ninetyThreeCM_3659
      · exact prime_ninetyThreeCM_6733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 596882146717) ^ 298441073358 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 596882146717) ^ 198960715572 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 596882146717) ^ 886897692 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 596882146717) ^ 163127124 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 596882146717) ^ 88650252 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_602203799933 : Nat.Prime 602203799933 := by
  apply lucas_primality 602203799933 (3 : ZMod 602203799933)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (131, 1), (23453957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (131, 1), (23453957, 1)] : List FactorBlock).map factorBlockValue).prod) = 602203799933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_131
      · exact prime_ninetyThreeCM_23453957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 602203799933) ^ 301101899966 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 602203799933) ^ 86029114276 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 602203799933) ^ 4596975572 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 602203799933) ^ 25676 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_922204651829 : Nat.Prime 922204651829 := by
  apply lucas_primality 922204651829 (2 : ZMod 922204651829)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (3158235109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (3158235109, 1)] : List FactorBlock).map factorBlockValue).prod) = 922204651829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_73
      · exact prime_ninetyThreeCM_3158235109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 922204651829) ^ 461102325914 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 922204651829) ^ 12632940436 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 922204651829) ^ 292 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1031393588131 : Nat.Prime 1031393588131 := by
  apply lucas_primality 1031393588131 (31 : ZMod 1031393588131)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (191, 1), (59999627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (191, 1), (59999627, 1)] : List FactorBlock).map factorBlockValue).prod) = 1031393588131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_191
      · exact prime_ninetyThreeCM_59999627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 1031393588131) ^ 515696794065 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (31 : ZMod 1031393588131) ^ 343797862710 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (31 : ZMod 1031393588131) ^ 206278717626 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (31 : ZMod 1031393588131) ^ 5399966430 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (31 : ZMod 1031393588131) ^ 17190 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1207148227073 : Nat.Prime 1207148227073 := by
  apply lucas_primality 1207148227073 (3 : ZMod 1207148227073)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (163, 1), (3727, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (163, 1), (3727, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1207148227073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_163
      · exact prime_ninetyThreeCM_3727
      · exact prime_ninetyThreeCM_3881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1207148227073) ^ 603574113536 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1207148227073) ^ 7405817344 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1207148227073) ^ 323892736 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1207148227073) ^ 311040512 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1561319351153 : Nat.Prime 1561319351153 := by
  apply lucas_primality 1561319351153 (3 : ZMod 1561319351153)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 2), (751, 1), (1073857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 2), (751, 1), (1073857, 1)] : List FactorBlock).map factorBlockValue).prod) = 1561319351153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_751
      · exact prime_ninetyThreeCM_1073857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1561319351153) ^ 780659675576 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1561319351153) ^ 141938122832 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1561319351153) ^ 2078987152 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1561319351153) ^ 1453936 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2249817570703 : Nat.Prime 2249817570703 := by
  apply lucas_primality 2249817570703 (3 : ZMod 2249817570703)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (9614605003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (9614605003, 1)] : List FactorBlock).map factorBlockValue).prod) = 2249817570703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_9614605003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2249817570703) ^ 1124908785351 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2249817570703) ^ 749939190234 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2249817570703) ^ 173062890054 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2249817570703) ^ 234 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2749089287369 : Nat.Prime 2749089287369 := by
  apply lucas_primality 2749089287369 (3 : ZMod 2749089287369)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (199, 1), (16765193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (199, 1), (16765193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2749089287369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_103
      · exact prime_ninetyThreeCM_199
      · exact prime_ninetyThreeCM_16765193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2749089287369) ^ 1374544643684 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2749089287369) ^ 26690187256 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2749089287369) ^ 13814519032 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2749089287369) ^ 163976 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_3994471272037 : Nat.Prime 3994471272037 := by
  apply lucas_primality 3994471272037 (5 : ZMod 3994471272037)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (37, 2), (347, 1), (100103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (37, 2), (347, 1), (100103, 1)] : List FactorBlock).map factorBlockValue).prod) = 3994471272037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_37
      · exact prime_ninetyThreeCM_347
      · exact prime_ninetyThreeCM_100103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3994471272037) ^ 1997235636018 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3994471272037) ^ 1331490424012 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3994471272037) ^ 570638753148 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3994471272037) ^ 107958683028 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3994471272037) ^ 11511444588 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 3994471272037) ^ 39903612 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_5218337696239 : Nat.Prime 5218337696239 := by
  apply lucas_primality 5218337696239 (3 : ZMod 5218337696239)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (289907649791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (289907649791, 1)] : List FactorBlock).map factorBlockValue).prod) = 5218337696239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_289907649791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5218337696239) ^ 2609168848119 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5218337696239) ^ 1739445898746 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5218337696239) ^ 18 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_5225476319551 : Nat.Prime 5225476319551 := by
  apply lucas_primality 5225476319551 (3 : ZMod 5225476319551)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (19, 1), (611166821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (19, 1), (611166821, 1)] : List FactorBlock).map factorBlockValue).prod) = 5225476319551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_611166821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5225476319551) ^ 2612738159775 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5225476319551) ^ 1741825439850 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5225476319551) ^ 1045095263910 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5225476319551) ^ 275025069450 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 5225476319551) ^ 8550 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_6365599255817 : Nat.Prime 6365599255817 := by
  apply lucas_primality 6365599255817 (3 : ZMod 6365599255817)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (89, 1), (525908729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (89, 1), (525908729, 1)] : List FactorBlock).map factorBlockValue).prod) = 6365599255817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_89
      · exact prime_ninetyThreeCM_525908729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6365599255817) ^ 3182799627908 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6365599255817) ^ 374447015048 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6365599255817) ^ 71523587144 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 6365599255817) ^ 12104 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_8374340716367 : Nat.Prime 8374340716367 := by
  apply lucas_primality 8374340716367 (5 : ZMod 8374340716367)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (263, 1), (1237, 1), (12870493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (263, 1), (1237, 1), (12870493, 1)] : List FactorBlock).map factorBlockValue).prod) = 8374340716367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_263
      · exact prime_ninetyThreeCM_1237
      · exact prime_ninetyThreeCM_12870493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8374340716367) ^ 4187170358183 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 8374340716367) ^ 31841599682 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 8374340716367) ^ 6769879318 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 8374340716367) ^ 650662 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_9187067985853 : Nat.Prime 9187067985853 := by
  apply lucas_primality 9187067985853 (5 : ZMod 9187067985853)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (26399620649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (26399620649, 1)] : List FactorBlock).map factorBlockValue).prod) = 9187067985853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_26399620649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9187067985853) ^ 4593533992926 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9187067985853) ^ 3062355995284 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9187067985853) ^ 316795447788 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9187067985853) ^ 348 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_9371772079667 : Nat.Prime 9371772079667 := by
  apply lucas_primality 9371772079667 (2 : ZMod 9371772079667)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (227, 1), (1153, 1), (17903443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (227, 1), (1153, 1), (17903443, 1)] : List FactorBlock).map factorBlockValue).prod) = 9371772079667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_227
      · exact prime_ninetyThreeCM_1153
      · exact prime_ninetyThreeCM_17903443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9371772079667) ^ 4685886039833 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9371772079667) ^ 41285339558 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9371772079667) ^ 8128163122 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9371772079667) ^ 523462 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_9473947763807 : Nat.Prime 9473947763807 := by
  apply lucas_primality 9473947763807 (5 : ZMod 9473947763807)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (311, 1), (601, 1), (1333867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (311, 1), (601, 1), (1333867, 1)] : List FactorBlock).map factorBlockValue).prod) = 9473947763807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_311
      · exact prime_ninetyThreeCM_601
      · exact prime_ninetyThreeCM_1333867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9473947763807) ^ 4736973881903 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9473947763807) ^ 498628829674 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9473947763807) ^ 30462854546 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9473947763807) ^ 15763640206 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 9473947763807) ^ 7102618 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_9703136947211 : Nat.Prime 9703136947211 := by
  apply lucas_primality 9703136947211 (2 : ZMod 9703136947211)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (193, 1), (718218871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (193, 1), (718218871, 1)] : List FactorBlock).map factorBlockValue).prod) = 9703136947211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_193
      · exact prime_ninetyThreeCM_718218871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9703136947211) ^ 4851568473605 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703136947211) ^ 1940627389442 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703136947211) ^ 1386162421030 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703136947211) ^ 50275320970 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703136947211) ^ 13510 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_11866082938319 : Nat.Prime 11866082938319 := by
  apply lucas_primality 11866082938319 (11 : ZMod 11866082938319)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (59, 1), (9931, 1), (46663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (59, 1), (9931, 1), (46663, 1)] : List FactorBlock).map factorBlockValue).prod) = 11866082938319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_31
      · exact prime_ninetyThreeCM_59
      · exact prime_ninetyThreeCM_9931
      · exact prime_ninetyThreeCM_46663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11866082938319) ^ 5933041469159 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 11866082938319) ^ 1695154705474 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 11866082938319) ^ 382776868978 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 11866082938319) ^ 201120049802 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 11866082938319) ^ 1194852778 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 11866082938319) ^ 254293186 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_14317110250489 : Nat.Prime 14317110250489 := by
  apply lucas_primality 14317110250489 (11 : ZMod 14317110250489)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (255859, 1), (777181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (255859, 1), (777181, 1)] : List FactorBlock).map factorBlockValue).prod) = 14317110250489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_255859
      · exact prime_ninetyThreeCM_777181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 14317110250489) ^ 7158555125244 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 14317110250489) ^ 4772370083496 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 14317110250489) ^ 55957032 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 14317110250489) ^ 18421848 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_15187815955859 : Nat.Prime 15187815955859 := by
  apply lucas_primality 15187815955859 (2 : ZMod 15187815955859)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (145283, 1), (574393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (145283, 1), (574393, 1)] : List FactorBlock).map factorBlockValue).prod) = 15187815955859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_145283
      · exact prime_ninetyThreeCM_574393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15187815955859) ^ 7593907977929 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15187815955859) ^ 2169687993694 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15187815955859) ^ 1168293535066 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15187815955859) ^ 104539526 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15187815955859) ^ 26441506 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_16234628797019 : Nat.Prime 16234628797019 := by
  apply lucas_primality 16234628797019 (2 : ZMod 16234628797019)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (6211, 1), (16543361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (6211, 1), (16543361, 1)] : List FactorBlock).map factorBlockValue).prod) = 16234628797019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_79
      · exact prime_ninetyThreeCM_6211
      · exact prime_ninetyThreeCM_16543361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16234628797019) ^ 8117314398509 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16234628797019) ^ 205501630342 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16234628797019) ^ 2613851038 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16234628797019) ^ 981338 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_20071726007701 : Nat.Prime 20071726007701 := by
  apply lucas_primality 20071726007701 (2 : ZMod 20071726007701)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (109, 1), (359, 1), (1709789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (109, 1), (359, 1), (1709789, 1)] : List FactorBlock).map factorBlockValue).prod) = 20071726007701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_109
      · exact prime_ninetyThreeCM_359
      · exact prime_ninetyThreeCM_1709789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20071726007701) ^ 10035863003850 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20071726007701) ^ 6690575335900 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20071726007701) ^ 4014345201540 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20071726007701) ^ 184144275300 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20071726007701) ^ 55910100300 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 20071726007701) ^ 11739300 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_20924418513353 : Nat.Prime 20924418513353 := by
  apply lucas_primality 20924418513353 (3 : ZMod 20924418513353)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1018643, 1), (2567683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1018643, 1), (2567683, 1)] : List FactorBlock).map factorBlockValue).prod) = 20924418513353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_1018643
      · exact prime_ninetyThreeCM_2567683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20924418513353) ^ 10462209256676 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 20924418513353) ^ 20541464 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 20924418513353) ^ 8149144 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_29322703660609 : Nat.Prime 29322703660609 := by
  apply lucas_primality 29322703660609 (11 : ZMod 29322703660609)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (5656385737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (5656385737, 1)] : List FactorBlock).map factorBlockValue).prod) = 29322703660609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5656385737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 29322703660609) ^ 14661351830304 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 29322703660609) ^ 9774234553536 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 29322703660609) ^ 5184 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_30308805552499 : Nat.Prime 30308805552499 := by
  apply lucas_primality 30308805552499 (2 : ZMod 30308805552499)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (459224326553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (459224326553, 1)] : List FactorBlock).map factorBlockValue).prod) = 30308805552499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_459224326553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30308805552499) ^ 15154402776249 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30308805552499) ^ 10102935184166 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30308805552499) ^ 2755345959318 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 30308805552499) ^ 66 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_39119374630027 : Nat.Prime 39119374630027 := by
  apply lucas_primality 39119374630027 (2 : ZMod 39119374630027)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (31, 1), (288503729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (31, 1), (288503729, 1)] : List FactorBlock).map factorBlockValue).prod) = 39119374630027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_31
      · exact prime_ninetyThreeCM_288503729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39119374630027) ^ 19559687315013 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 39119374630027) ^ 13039791543342 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 39119374630027) ^ 1261915310646 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 39119374630027) ^ 135594 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_54346880552329 : Nat.Prime 54346880552329 := by
  apply lucas_primality 54346880552329 (19 : ZMod 54346880552329)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 3), (13, 1), (41, 1), (1376257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 3), (13, 1), (41, 1), (1376257, 1)] : List FactorBlock).map factorBlockValue).prod) = 54346880552329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_41
      · exact prime_ninetyThreeCM_1376257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 54346880552329) ^ 27173440276164 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (19 : ZMod 54346880552329) ^ 18115626850776 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (19 : ZMod 54346880552329) ^ 7763840078904 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (19 : ZMod 54346880552329) ^ 4180529273256 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (19 : ZMod 54346880552329) ^ 1325533672008 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (19 : ZMod 54346880552329) ^ 39488904 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_61966689285511 : Nat.Prime 61966689285511 := by
  apply lucas_primality 61966689285511 (3 : ZMod 61966689285511)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (229506256613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (229506256613, 1)] : List FactorBlock).map factorBlockValue).prod) = 61966689285511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_229506256613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 61966689285511) ^ 30983344642755 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 61966689285511) ^ 20655563095170 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 61966689285511) ^ 12393337857102 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 61966689285511) ^ 270 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_66036415028347 : Nat.Prime 66036415028347 := by
  apply lucas_primality 66036415028347 (2 : ZMod 66036415028347)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 2), (163, 1), (51036959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 2), (163, 1), (51036959, 1)] : List FactorBlock).map factorBlockValue).prod) = 66036415028347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_163
      · exact prime_ninetyThreeCM_51036959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66036415028347) ^ 33018207514173 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66036415028347) ^ 22012138342782 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66036415028347) ^ 9433773575478 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66036415028347) ^ 405131380542 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 66036415028347) ^ 1293894 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_69839685566383 : Nat.Prime 69839685566383 := by
  apply lucas_primality 69839685566383 (3 : ZMod 69839685566383)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (449, 1), (25924159453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (449, 1), (25924159453, 1)] : List FactorBlock).map factorBlockValue).prod) = 69839685566383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_449
      · exact prime_ninetyThreeCM_25924159453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 69839685566383) ^ 34919842783191 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 69839685566383) ^ 23279895188794 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 69839685566383) ^ 155544956718 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 69839685566383) ^ 2694 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_72553713824923 : Nat.Prime 72553713824923 := by
  apply lucas_primality 72553713824923 (3 : ZMod 72553713824923)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (4513, 1), (243584909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (4513, 1), (243584909, 1)] : List FactorBlock).map factorBlockValue).prod) = 72553713824923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_4513
      · exact prime_ninetyThreeCM_243584909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72553713824923) ^ 36276856912461 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 72553713824923) ^ 24184571274974 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 72553713824923) ^ 6595792165902 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 72553713824923) ^ 16076603994 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 72553713824923) ^ 297858 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_94871854291729 : Nat.Prime 94871854291729 := by
  apply lucas_primality 94871854291729 (13 : ZMod 94871854291729)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (6317, 1), (15749, 1), (19867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (6317, 1), (15749, 1), (19867, 1)] : List FactorBlock).map factorBlockValue).prod) = 94871854291729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_6317
      · exact prime_ninetyThreeCM_15749
      · exact prime_ninetyThreeCM_19867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 94871854291729) ^ 47435927145864 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 94871854291729) ^ 31623951430576 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 94871854291729) ^ 15018498384 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 94871854291729) ^ 6023992272 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 94871854291729) ^ 4775348784 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_105335765032661 : Nat.Prime 105335765032661 := by
  apply lucas_primality 105335765032661 (2 : ZMod 105335765032661)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (101, 1), (98143, 1), (531331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (101, 1), (98143, 1), (531331, 1)] : List FactorBlock).map factorBlockValue).prod) = 105335765032661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_101
      · exact prime_ninetyThreeCM_98143
      · exact prime_ninetyThreeCM_531331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105335765032661) ^ 52667882516330 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 105335765032661) ^ 21067153006532 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 105335765032661) ^ 1042928366660 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 105335765032661) ^ 1073288620 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 105335765032661) ^ 198248860 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_109412414208193 : Nat.Prime 109412414208193 := by
  apply lucas_primality 109412414208193 (5 : ZMod 109412414208193)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (29, 1), (20887, 1), (940787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (29, 1), (20887, 1), (940787, 1)] : List FactorBlock).map factorBlockValue).prod) = 109412414208193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_20887
      · exact prime_ninetyThreeCM_940787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 109412414208193) ^ 54706207104096 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 109412414208193) ^ 36470804736064 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 109412414208193) ^ 3772841869248 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 109412414208193) ^ 5238302016 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 109412414208193) ^ 116298816 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_111436504554299 : Nat.Prime 111436504554299 := by
  apply lucas_primality 111436504554299 (2 : ZMod 111436504554299)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (17, 1), (83, 1), (512837467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (17, 1), (83, 1), (512837467, 1)] : List FactorBlock).map factorBlockValue).prod) = 111436504554299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_83
      · exact prime_ninetyThreeCM_512837467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 111436504554299) ^ 55718252277149 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 111436504554299) ^ 15919500650614 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 111436504554299) ^ 10130591323118 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 111436504554299) ^ 6555088503194 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 111436504554299) ^ 1342608488606 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 111436504554299) ^ 217294 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_117290814642437 : Nat.Prime 117290814642437 := by
  apply lucas_primality 117290814642437 (2 : ZMod 117290814642437)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29322703660609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29322703660609, 1)] : List FactorBlock).map factorBlockValue).prod) = 117290814642437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_29322703660609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 117290814642437) ^ 58645407321218 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 117290814642437) ^ 4 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_120430356046207 : Nat.Prime 120430356046207 := by
  apply lucas_primality 120430356046207 (3 : ZMod 120430356046207)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (20071726007701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (20071726007701, 1)] : List FactorBlock).map factorBlockValue).prod) = 120430356046207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_20071726007701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 120430356046207) ^ 60215178023103 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 120430356046207) ^ 40143452015402 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 120430356046207) ^ 6 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_123383010748223 : Nat.Prime 123383010748223 := by
  apply lucas_primality 123383010748223 (5 : ZMod 123383010748223)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (276643521857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (276643521857, 1)] : List FactorBlock).map factorBlockValue).prod) = 123383010748223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_223
      · exact prime_ninetyThreeCM_276643521857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 123383010748223) ^ 61691505374111 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 123383010748223) ^ 553287043714 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 123383010748223) ^ 446 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_146023799455889 : Nat.Prime 146023799455889 := by
  apply lucas_primality 146023799455889 (3 : ZMod 146023799455889)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (27697, 1), (329511769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (27697, 1), (329511769, 1)] : List FactorBlock).map factorBlockValue).prod) = 146023799455889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_27697
      · exact prime_ninetyThreeCM_329511769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 146023799455889) ^ 73011899727944 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 146023799455889) ^ 5272188304 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 146023799455889) ^ 443152 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_150494677223939 : Nat.Prime 150494677223939 := by
  apply lucas_primality 150494677223939 (2 : ZMod 150494677223939)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (852323, 1), (88285003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (852323, 1), (88285003, 1)] : List FactorBlock).map factorBlockValue).prod) = 150494677223939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_852323
      · exact prime_ninetyThreeCM_88285003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 150494677223939) ^ 75247338611969 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 150494677223939) ^ 176570006 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 150494677223939) ^ 1704646 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_165743408162407 : Nat.Prime 165743408162407 := by
  apply lucas_primality 165743408162407 (3 : ZMod 165743408162407)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (43, 1), (55207, 1), (375371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (43, 1), (55207, 1), (375371, 1)] : List FactorBlock).map factorBlockValue).prod) = 165743408162407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_31
      · exact prime_ninetyThreeCM_43
      · exact prime_ninetyThreeCM_55207
      · exact prime_ninetyThreeCM_375371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 165743408162407) ^ 82871704081203 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 165743408162407) ^ 55247802720802 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 165743408162407) ^ 5346561553626 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 165743408162407) ^ 3854497864242 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 165743408162407) ^ 3002217258 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 165743408162407) ^ 441545586 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_167486814327341 : Nat.Prime 167486814327341 := by
  apply lucas_primality 167486814327341 (2 : ZMod 167486814327341)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (8374340716367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (8374340716367, 1)] : List FactorBlock).map factorBlockValue).prod) = 167486814327341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_8374340716367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 167486814327341) ^ 83743407163670 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 167486814327341) ^ 33497362865468 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 167486814327341) ^ 20 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_249385395292279 : Nat.Prime 249385395292279 := by
  apply lucas_primality 249385395292279 (3 : ZMod 249385395292279)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (272539, 1), (21786781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (272539, 1), (21786781, 1)] : List FactorBlock).map factorBlockValue).prod) = 249385395292279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_272539
      · exact prime_ninetyThreeCM_21786781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 249385395292279) ^ 124692697646139 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 249385395292279) ^ 83128465097426 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 249385395292279) ^ 35626485041754 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 249385395292279) ^ 915044802 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 249385395292279) ^ 11446638 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_288460537436713 : Nat.Prime 288460537436713 := by
  apply lucas_primality 288460537436713 (13 : ZMod 288460537436713)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (103, 1), (179, 1), (197, 1), (3309167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (103, 1), (179, 1), (197, 1), (3309167, 1)] : List FactorBlock).map factorBlockValue).prod) = 288460537436713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_103
      · exact prime_ninetyThreeCM_179
      · exact prime_ninetyThreeCM_197
      · exact prime_ninetyThreeCM_3309167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 288460537436713) ^ 144230268718356 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 288460537436713) ^ 96153512478904 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 288460537436713) ^ 2800587742104 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 288460537436713) ^ 1611511382328 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 288460537436713) ^ 1464266687496 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 288460537436713) ^ 87170136 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_407587152924979 : Nat.Prime 407587152924979 := by
  apply lucas_primality 407587152924979 (2 : ZMod 407587152924979)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (5225476319551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (5225476319551, 1)] : List FactorBlock).map factorBlockValue).prod) = 407587152924979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_5225476319551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 407587152924979) ^ 203793576462489 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 407587152924979) ^ 135862384308326 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 407587152924979) ^ 31352857917306 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 407587152924979) ^ 78 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_434942935312133 : Nat.Prime 434942935312133 := by
  apply lucas_primality 434942935312133 (2 : ZMod 434942935312133)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1060201, 1), (7889341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1060201, 1), (7889341, 1)] : List FactorBlock).map factorBlockValue).prod) = 434942935312133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_1060201
      · exact prime_ninetyThreeCM_7889341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 434942935312133) ^ 217471467656066 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 434942935312133) ^ 33457148870164 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 434942935312133) ^ 410245732 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 434942935312133) ^ 55130452 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_459213717269033 : Nat.Prime 459213717269033 := by
  apply lucas_primality 459213717269033 (3 : ZMod 459213717269033)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (5218337696239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (5218337696239, 1)] : List FactorBlock).map factorBlockValue).prod) = 459213717269033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_5218337696239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 459213717269033) ^ 229606858634516 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 459213717269033) ^ 41746701569912 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 459213717269033) ^ 88 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_496852464104723 : Nat.Prime 496852464104723 := by
  apply lucas_primality 496852464104723 (2 : ZMod 496852464104723)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (41, 1), (2971, 1), (6393229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (41, 1), (2971, 1), (6393229, 1)] : List FactorBlock).map factorBlockValue).prod) = 496852464104723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_41
      · exact prime_ninetyThreeCM_2971
      · exact prime_ninetyThreeCM_6393229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 496852464104723) ^ 248426232052361 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 496852464104723) ^ 45168405827702 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 496852464104723) ^ 17132843589818 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 496852464104723) ^ 12118352783042 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 496852464104723) ^ 167234084182 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 496852464104723) ^ 77715418 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_680046078371171 : Nat.Prime 680046078371171 := by
  apply lucas_primality 680046078371171 (2 : ZMod 680046078371171)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (41, 1), (79, 1), (677, 1), (632911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (41, 1), (79, 1), (677, 1), (632911, 1)] : List FactorBlock).map factorBlockValue).prod) = 680046078371171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_41
      · exact prime_ninetyThreeCM_79
      · exact prime_ninetyThreeCM_677
      · exact prime_ninetyThreeCM_632911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 680046078371171) ^ 340023039185585 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 680046078371171) ^ 136009215674234 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 680046078371171) ^ 97149439767310 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 680046078371171) ^ 16586489716370 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 680046078371171) ^ 8608178207230 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 680046078371171) ^ 1004499377210 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 680046078371171) ^ 1074473470 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_918427434538067 : Nat.Prime 918427434538067 := by
  apply lucas_primality 918427434538067 (2 : ZMod 918427434538067)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (459213717269033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (459213717269033, 1)] : List FactorBlock).map factorBlockValue).prod) = 918427434538067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_459213717269033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 918427434538067) ^ 459213717269033 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 918427434538067) ^ 2 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1248203156071853 : Nat.Prime 1248203156071853 := by
  apply lucas_primality 1248203156071853 (3 : ZMod 1248203156071853)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (173, 1), (41947948517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (173, 1), (41947948517, 1)] : List FactorBlock).map factorBlockValue).prod) = 1248203156071853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_43
      · exact prime_ninetyThreeCM_173
      · exact prime_ninetyThreeCM_41947948517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1248203156071853) ^ 624101578035926 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1248203156071853) ^ 29027980373764 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1248203156071853) ^ 7215047144924 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1248203156071853) ^ 29756 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_3095277830883149 : Nat.Prime 3095277830883149 := by
  apply lucas_primality 3095277830883149 (2 : ZMod 3095277830883149)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4111, 1), (208961, 1), (900797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4111, 1), (208961, 1), (900797, 1)] : List FactorBlock).map factorBlockValue).prod) = 3095277830883149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_4111
      · exact prime_ninetyThreeCM_208961
      · exact prime_ninetyThreeCM_900797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3095277830883149) ^ 1547638915441574 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3095277830883149) ^ 752925767668 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3095277830883149) ^ 14812705868 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 3095277830883149) ^ 3436154684 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_4075871529249791 : Nat.Prime 4075871529249791 := by
  apply lucas_primality 4075871529249791 (13 : ZMod 4075871529249791)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (407587152924979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (407587152924979, 1)] : List FactorBlock).map factorBlockValue).prod) = 4075871529249791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_407587152924979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 4075871529249791) ^ 2037935764624895 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 4075871529249791) ^ 815174305849958 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 4075871529249791) ^ 10 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_4441788386936029 : Nat.Prime 4441788386936029 := by
  apply lucas_primality 4441788386936029 (2 : ZMod 4441788386936029)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (123383010748223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (123383010748223, 1)] : List FactorBlock).map factorBlockValue).prod) = 4441788386936029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_123383010748223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4441788386936029) ^ 2220894193468014 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4441788386936029) ^ 1480596128978676 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 4441788386936029) ^ 36 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_4486585091262427 : Nat.Prime 4486585091262427 := by
  apply lucas_primality 4486585091262427 (3 : ZMod 4486585091262427)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (79, 1), (8233, 1), (12362221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (79, 1), (8233, 1), (12362221, 1)] : List FactorBlock).map factorBlockValue).prod) = 4486585091262427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_31
      · exact prime_ninetyThreeCM_79
      · exact prime_ninetyThreeCM_8233
      · exact prime_ninetyThreeCM_12362221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4486585091262427) ^ 2243292545631213 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4486585091262427) ^ 1495528363754142 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4486585091262427) ^ 144728551331046 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4486585091262427) ^ 56792216345094 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4486585091262427) ^ 544951426122 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 4486585091262427) ^ 362927106 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_4553849006002993 : Nat.Prime 4553849006002993 := by
  apply lucas_primality 4553849006002993 (10 : ZMod 4553849006002993)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (94871854291729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (94871854291729, 1)] : List FactorBlock).map factorBlockValue).prod) = 4553849006002993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_94871854291729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 4553849006002993) ^ 2276924503001496 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (10 : ZMod 4553849006002993) ^ 1517949668667664 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (10 : ZMod 4553849006002993) ^ 48 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_7012779006425371 : Nat.Prime 7012779006425371 := by
  apply lucas_primality 7012779006425371 (3 : ZMod 7012779006425371)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (111103, 1), (2103987293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (111103, 1), (2103987293, 1)] : List FactorBlock).map factorBlockValue).prod) = 7012779006425371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_111103
      · exact prime_ninetyThreeCM_2103987293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7012779006425371) ^ 3506389503212685 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7012779006425371) ^ 2337593002141790 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7012779006425371) ^ 1402555801285074 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7012779006425371) ^ 63119618790 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7012779006425371) ^ 3333090 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_23895130268707067 : Nat.Prime 23895130268707067 := by
  apply lucas_primality 23895130268707067 (2 : ZMod 23895130268707067)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (613, 1), (52361, 1), (372229681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (613, 1), (52361, 1), (372229681, 1)] : List FactorBlock).map factorBlockValue).prod) = 23895130268707067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_613
      · exact prime_ninetyThreeCM_52361
      · exact prime_ninetyThreeCM_372229681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23895130268707067) ^ 11947565134353533 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 23895130268707067) ^ 38980636653682 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 23895130268707067) ^ 456353588906 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 23895130268707067) ^ 64194586 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_43226695692678457 : Nat.Prime 43226695692678457 := by
  apply lucas_primality 43226695692678457 (5 : ZMod 43226695692678457)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (16633, 1), (5156451233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (16633, 1), (5156451233, 1)] : List FactorBlock).map factorBlockValue).prod) = 43226695692678457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_16633
      · exact prime_ninetyThreeCM_5156451233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 43226695692678457) ^ 21613347846339228 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 43226695692678457) ^ 14408898564226152 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 43226695692678457) ^ 6175242241811208 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 43226695692678457) ^ 2598851421432 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 43226695692678457) ^ 8383032 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_49779463569374579 : Nat.Prime 49779463569374579 := by
  apply lucas_primality 49779463569374579 (2 : ZMod 49779463569374579)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (37, 1), (2249817570703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (37, 1), (2249817570703, 1)] : List FactorBlock).map factorBlockValue).prod) = 49779463569374579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_23
      · exact prime_ninetyThreeCM_37
      · exact prime_ninetyThreeCM_2249817570703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49779463569374579) ^ 24889731784687289 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 49779463569374579) ^ 3829189505336506 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 49779463569374579) ^ 2164324503016286 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 49779463569374579) ^ 1345390907280394 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 49779463569374579) ^ 22126 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_72649435754780917 : Nat.Prime 72649435754780917 := by
  apply lucas_primality 72649435754780917 (5 : ZMod 72649435754780917)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (15889, 1), (5219532119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (15889, 1), (5219532119, 1)] : List FactorBlock).map factorBlockValue).prod) = 72649435754780917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_73
      · exact prime_ninetyThreeCM_15889
      · exact prime_ninetyThreeCM_5219532119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 72649435754780917) ^ 36324717877390458 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 72649435754780917) ^ 24216478584926972 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 72649435754780917) ^ 995197750065492 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 72649435754780917) ^ 4572310136244 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 72649435754780917) ^ 13918764 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_88204520980322759 : Nat.Prime 88204520980322759 := by
  apply lucas_primality 88204520980322759 (11 : ZMod 88204520980322759)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (9554123, 1), (419640443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (9554123, 1), (419640443, 1)] : List FactorBlock).map factorBlockValue).prod) = 88204520980322759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_9554123
      · exact prime_ninetyThreeCM_419640443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 88204520980322759) ^ 44102260490161379 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 88204520980322759) ^ 8018592816392978 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 88204520980322759) ^ 9232089746 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 88204520980322759) ^ 210190706 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_93058673915201671 : Nat.Prime 93058673915201671 := by
  apply lucas_primality 93058673915201671 (6 : ZMod 93058673915201671)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (2683, 1), (3191, 1), (9290167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (2683, 1), (3191, 1), (9290167, 1)] : List FactorBlock).map factorBlockValue).prod) = 93058673915201671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_2683
      · exact prime_ninetyThreeCM_3191
      · exact prime_ninetyThreeCM_9290167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 93058673915201671) ^ 46529336957600835 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 93058673915201671) ^ 31019557971733890 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 93058673915201671) ^ 18611734783040334 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 93058673915201671) ^ 7158359531938590 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 93058673915201671) ^ 34684559789490 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 93058673915201671) ^ 29162856131370 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 93058673915201671) ^ 10016900010 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_106343443608552607 : Nat.Prime 106343443608552607 := by
  apply lucas_primality 106343443608552607 (6 : ZMod 106343443608552607)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (7395413, 1), (32830249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (7395413, 1), (32830249, 1)] : List FactorBlock).map factorBlockValue).prod) = 106343443608552607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_73
      · exact prime_ninetyThreeCM_7395413
      · exact prime_ninetyThreeCM_32830249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 106343443608552607) ^ 53171721804276303 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 106343443608552607) ^ 35447814536184202 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 106343443608552607) ^ 1456759501487022 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 106343443608552607) ^ 14379649062 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 106343443608552607) ^ 3239190894 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_106604133947357197 : Nat.Prime 106604133947357197 := by
  apply lucas_primality 106604133947357197 (2 : ZMod 106604133947357197)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17399171, 1), (510580523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17399171, 1), (510580523, 1)] : List FactorBlock).map factorBlockValue).prod) = 106604133947357197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_17399171
      · exact prime_ninetyThreeCM_510580523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 106604133947357197) ^ 53302066973678598 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 106604133947357197) ^ 35534711315785732 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 106604133947357197) ^ 6126966276 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 106604133947357197) ^ 208790052 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_113782621333386793 : Nat.Prime 113782621333386793 := by
  apply lucas_primality 113782621333386793 (11 : ZMod 113782621333386793)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (71, 1), (103, 1), (8461, 1), (76620931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (71, 1), (103, 1), (8461, 1), (76620931, 1)] : List FactorBlock).map factorBlockValue).prod) = 113782621333386793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_71
      · exact prime_ninetyThreeCM_103
      · exact prime_ninetyThreeCM_8461
      · exact prime_ninetyThreeCM_76620931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 113782621333386793) ^ 56891310666693396 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 113782621333386793) ^ 37927540444462264 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 113782621333386793) ^ 1602572131456152 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 113782621333386793) ^ 1104685644013464 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 113782621333386793) ^ 13447892841672 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 113782621333386793) ^ 1485007032 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_119226052485744931 : Nat.Prime 119226052485744931 := by
  apply lucas_primality 119226052485744931 (3 : ZMod 119226052485744931)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (120430356046207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (120430356046207, 1)] : List FactorBlock).map factorBlockValue).prod) = 119226052485744931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_120430356046207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 119226052485744931) ^ 59613026242872465 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 119226052485744931) ^ 39742017495248310 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 119226052485744931) ^ 23845210497148986 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 119226052485744931) ^ 10838732044158630 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 119226052485744931) ^ 990 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_124843811367592799 : Nat.Prime 124843811367592799 := by
  apply lucas_primality 124843811367592799 (11 : ZMod 124843811367592799)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (950633, 1), (123196091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (950633, 1), (123196091, 1)] : List FactorBlock).map factorBlockValue).prod) = 124843811367592799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_41
      · exact prime_ninetyThreeCM_950633
      · exact prime_ninetyThreeCM_123196091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 124843811367592799) ^ 62421905683796399 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 124843811367592799) ^ 9603370105199446 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 124843811367592799) ^ 3044971008965678 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 124843811367592799) ^ 131327033006 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 124843811367592799) ^ 1013374778 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_155890056773180879 : Nat.Prime 155890056773180879 := by
  apply lucas_primality 155890056773180879 (7 : ZMod 155890056773180879)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8317, 1), (9371772079667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8317, 1), (9371772079667, 1)] : List FactorBlock).map factorBlockValue).prod) = 155890056773180879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_8317
      · exact prime_ninetyThreeCM_9371772079667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 155890056773180879) ^ 77945028386590439 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 155890056773180879) ^ 18743544159334 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 155890056773180879) ^ 16634 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_168036553526914873 : Nat.Prime 168036553526914873 := by
  apply lucas_primality 168036553526914873 (7 : ZMod 168036553526914873)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (23, 1), (1444447, 1), (70249271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (23, 1), (1444447, 1), (70249271, 1)] : List FactorBlock).map factorBlockValue).prod) = 168036553526914873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_23
      · exact prime_ninetyThreeCM_1444447
      · exact prime_ninetyThreeCM_70249271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 168036553526914873) ^ 84018276763457436 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 168036553526914873) ^ 56012184508971624 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 168036553526914873) ^ 7305937109865864 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 168036553526914873) ^ 116332792776 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 168036553526914873) ^ 2392004232 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_218539538681504981 : Nat.Prime 218539538681504981 := by
  apply lucas_primality 218539538681504981 (2 : ZMod 218539538681504981)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (137, 1), (2371, 1), (23099, 1), (1456313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (137, 1), (2371, 1), (23099, 1), (1456313, 1)] : List FactorBlock).map factorBlockValue).prod) = 218539538681504981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_137
      · exact prime_ninetyThreeCM_2371
      · exact prime_ninetyThreeCM_23099
      · exact prime_ninetyThreeCM_1456313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 218539538681504981) ^ 109269769340752490 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 218539538681504981) ^ 43707907736300996 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 218539538681504981) ^ 1595179114463540 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 218539538681504981) ^ 92171884724380 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 218539538681504981) ^ 9460995657020 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 218539538681504981) ^ 150063577460 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_227017124353803103 : Nat.Prime 227017124353803103 := by
  apply lucas_primality 227017124353803103 (3 : ZMod 227017124353803103)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (73, 1), (2111, 1), (22320483049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (73, 1), (2111, 1), (22320483049, 1)] : List FactorBlock).map factorBlockValue).prod) = 227017124353803103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_73
      · exact prime_ninetyThreeCM_2111
      · exact prime_ninetyThreeCM_22320483049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 227017124353803103) ^ 113508562176901551 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 227017124353803103) ^ 75672374784601034 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 227017124353803103) ^ 20637920395800282 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 227017124353803103) ^ 3109823621284974 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 227017124353803103) ^ 107540087330082 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 227017124353803103) ^ 10170798 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_278007211591231127 : Nat.Prime 278007211591231127 := by
  apply lucas_primality 278007211591231127 (5 : ZMod 278007211591231127)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (89, 1), (3994471272037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (89, 1), (3994471272037, 1)] : List FactorBlock).map factorBlockValue).prod) = 278007211591231127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_23
      · exact prime_ninetyThreeCM_89
      · exact prime_ninetyThreeCM_3994471272037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 278007211591231127) ^ 139003605795615563 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 278007211591231127) ^ 16353365387719478 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 278007211591231127) ^ 12087270069183962 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 278007211591231127) ^ 3123676534732934 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 278007211591231127) ^ 69598 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_324699784670547259 : Nat.Prime 324699784670547259 := by
  apply lucas_primality 324699784670547259 (2 : ZMod 324699784670547259)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (31, 1), (249385395292279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (31, 1), (249385395292279, 1)] : List FactorBlock).map factorBlockValue).prod) = 324699784670547259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_31
      · exact prime_ninetyThreeCM_249385395292279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 324699784670547259) ^ 162349892335273629 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699784670547259) ^ 108233261556849086 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699784670547259) ^ 46385683524363894 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699784670547259) ^ 10474186602275718 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699784670547259) ^ 1302 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_382625267796556693 : Nat.Prime 382625267796556693 := by
  apply lucas_primality 382625267796556693 (5 : ZMod 382625267796556693)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1319, 1), (204431, 1), (118249919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1319, 1), (204431, 1), (118249919, 1)] : List FactorBlock).map factorBlockValue).prod) = 382625267796556693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_1319
      · exact prime_ninetyThreeCM_204431
      · exact prime_ninetyThreeCM_118249919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 382625267796556693) ^ 191312633898278346 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 382625267796556693) ^ 127541755932185564 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 382625267796556693) ^ 290087390293068 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 382625267796556693) ^ 1871659717932 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 382625267796556693) ^ 3235733868 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_543730187669760349 : Nat.Prime 543730187669760349 := by
  apply lucas_primality 543730187669760349 (2 : ZMod 543730187669760349)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2791, 1), (16234628797019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2791, 1), (16234628797019, 1)] : List FactorBlock).map factorBlockValue).prod) = 543730187669760349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_2791
      · exact prime_ninetyThreeCM_16234628797019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 543730187669760349) ^ 271865093834880174 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 543730187669760349) ^ 181243395889920116 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 543730187669760349) ^ 194815545564228 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 543730187669760349) ^ 33492 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_599769631777058339 : Nat.Prime 599769631777058339 := by
  apply lucas_primality 599769631777058339 (2 : ZMod 599769631777058339)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (17663447, 1), (48646723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (17663447, 1), (48646723, 1)] : List FactorBlock).map factorBlockValue).prod) = 599769631777058339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_349
      · exact prime_ninetyThreeCM_17663447
      · exact prime_ninetyThreeCM_48646723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 599769631777058339) ^ 299884815888529169 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 599769631777058339) ^ 1718537626868362 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 599769631777058339) ^ 33955412654 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 599769631777058339) ^ 12329086006 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_612305747284069337 : Nat.Prime 612305747284069337 := by
  apply lucas_primality 612305747284069337 (3 : ZMod 612305747284069337)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5674181, 1), (13488857407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5674181, 1), (13488857407, 1)] : List FactorBlock).map factorBlockValue).prod) = 612305747284069337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5674181
      · exact prime_ninetyThreeCM_13488857407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 612305747284069337) ^ 306152873642034668 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 612305747284069337) ^ 107910859256 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 612305747284069337) ^ 45393448 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_677045584661649361 : Nat.Prime 677045584661649361 := by
  apply lucas_primality 677045584661649361 (23 : ZMod 677045584661649361)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (101, 1), (131431, 1), (212513969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (101, 1), (131431, 1), (212513969, 1)] : List FactorBlock).map factorBlockValue).prod) = 677045584661649361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_101
      · exact prime_ninetyThreeCM_131431
      · exact prime_ninetyThreeCM_212513969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 677045584661649361) ^ 338522792330824680 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (23 : ZMod 677045584661649361) ^ 225681861553883120 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (23 : ZMod 677045584661649361) ^ 135409116932329872 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (23 : ZMod 677045584661649361) ^ 6703421630313360 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (23 : ZMod 677045584661649361) ^ 5151338608560 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (23 : ZMod 677045584661649361) ^ 3185887440 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_984353225201483659 : Nat.Prime 984353225201483659 := by
  apply lucas_primality 984353225201483659 (2 : ZMod 984353225201483659)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 1), (419, 1), (809, 1), (3319, 1), (1064411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 1), (419, 1), (809, 1), (3319, 1), (1064411, 1)] : List FactorBlock).map factorBlockValue).prod) = 984353225201483659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_137
      · exact prime_ninetyThreeCM_419
      · exact prime_ninetyThreeCM_809
      · exact prime_ninetyThreeCM_3319
      · exact prime_ninetyThreeCM_1064411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 984353225201483659) ^ 492176612600741829 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 984353225201483659) ^ 328117741733827886 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 984353225201483659) ^ 7185060037967034 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 984353225201483659) ^ 2349291706924782 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 984353225201483659) ^ 1216753059581562 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 984353225201483659) ^ 296581267008582 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 984353225201483659) ^ 924786783678 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1168529376278726309 : Nat.Prime 1168529376278726309 := by
  apply lucas_primality 1168529376278726309 (2 : ZMod 1168529376278726309)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (17, 1), (23, 1), (9703136947211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (17, 1), (23, 1), (9703136947211, 1)] : List FactorBlock).map factorBlockValue).prod) = 1168529376278726309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_23
      · exact prime_ninetyThreeCM_9703136947211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1168529376278726309) ^ 584264688139363154 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1168529376278726309) ^ 166932768039818044 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1168529376278726309) ^ 106229943298066028 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1168529376278726309) ^ 68737022134042724 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1168529376278726309) ^ 50805625055596796 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1168529376278726309) ^ 120428 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1765387000332731977 : Nat.Prime 1765387000332731977 := by
  apply lucas_primality 1765387000332731977 (5 : ZMod 1765387000332731977)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (19, 1), (41, 1), (26561, 1), (209121113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (19, 1), (41, 1), (26561, 1), (209121113, 1)] : List FactorBlock).map factorBlockValue).prod) = 1765387000332731977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_41
      · exact prime_ninetyThreeCM_26561
      · exact prime_ninetyThreeCM_209121113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1765387000332731977) ^ 882693500166365988 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1765387000332731977) ^ 588462333444243992 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1765387000332731977) ^ 103846294137219528 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1765387000332731977) ^ 92915105280670104 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1765387000332731977) ^ 43058219520310536 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1765387000332731977) ^ 66465381587016 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1765387000332731977) ^ 8441935752 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2726349667220114407 : Nat.Prime 2726349667220114407 := by
  apply lucas_primality 2726349667220114407 (3 : ZMod 2726349667220114407)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (19, 1), (22013, 1), (7100779711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (19, 1), (22013, 1), (7100779711, 1)] : List FactorBlock).map factorBlockValue).prod) = 2726349667220114407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_22013
      · exact prime_ninetyThreeCM_7100779711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2726349667220114407) ^ 1363174833610057203 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2726349667220114407) ^ 908783222406704802 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2726349667220114407) ^ 160373509836477318 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2726349667220114407) ^ 143492087748427074 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2726349667220114407) ^ 123851799719262 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2726349667220114407) ^ 383950746 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2768254618187209913 : Nat.Prime 2768254618187209913 := by
  apply lucas_primality 2768254618187209913 (3 : ZMod 2768254618187209913)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2707, 1), (45667, 1), (2799144431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2707, 1), (45667, 1), (2799144431, 1)] : List FactorBlock).map factorBlockValue).prod) = 2768254618187209913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_2707
      · exact prime_ninetyThreeCM_45667
      · exact prime_ninetyThreeCM_2799144431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2768254618187209913) ^ 1384127309093604956 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2768254618187209913) ^ 1022628229843816 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2768254618187209913) ^ 60618271797736 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2768254618187209913) ^ 988964552 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_7021711111818577247 : Nat.Prime 7021711111818577247 := by
  apply lucas_primality 7021711111818577247 (5 : ZMod 7021711111818577247)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (773, 1), (1367, 1), (9511, 1), (349332323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (773, 1), (1367, 1), (9511, 1), (349332323, 1)] : List FactorBlock).map factorBlockValue).prod) = 7021711111818577247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_773
      · exact prime_ninetyThreeCM_1367
      · exact prime_ninetyThreeCM_9511
      · exact prime_ninetyThreeCM_349332323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7021711111818577247) ^ 3510855555909288623 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 7021711111818577247) ^ 9083714245560902 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 7021711111818577247) ^ 5136584573385938 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 7021711111818577247) ^ 738272643446386 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 7021711111818577247) ^ 20100376202 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_7141441459736996179 : Nat.Prime 7141441459736996179 := by
  apply lucas_primality 7141441459736996179 (2 : ZMod 7141441459736996179)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (3322757, 1), (2119577711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (3322757, 1), (2119577711, 1)] : List FactorBlock).map factorBlockValue).prod) = 7141441459736996179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_3322757
      · exact prime_ninetyThreeCM_2119577711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7141441459736996179) ^ 3570720729868498089 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7141441459736996179) ^ 2380480486578998726 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7141441459736996179) ^ 549341650748999706 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7141441459736996179) ^ 2149251798954 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 7141441459736996179) ^ 3369275598 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_10808287745953653409 : Nat.Prime 10808287745953653409 := by
  apply lucas_primality 10808287745953653409 (7 : ZMod 10808287745953653409)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (89010637, 1), (1264863779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (89010637, 1), (1264863779, 1)] : List FactorBlock).map factorBlockValue).prod) = 10808287745953653409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_89010637
      · exact prime_ninetyThreeCM_1264863779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 10808287745953653409) ^ 5404143872976826704 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 10808287745953653409) ^ 3602762581984551136 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 10808287745953653409) ^ 121426922784 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 10808287745953653409) ^ 8545021152 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_12258406965903184223 : Nat.Prime 12258406965903184223 := by
  apply lucas_primality 12258406965903184223 (5 : ZMod 12258406965903184223)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1217, 1), (712819, 1), (7065358357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1217, 1), (712819, 1), (7065358357, 1)] : List FactorBlock).map factorBlockValue).prod) = 12258406965903184223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_1217
      · exact prime_ninetyThreeCM_712819
      · exact prime_ninetyThreeCM_7065358357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12258406965903184223) ^ 6129203482951592111 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 12258406965903184223) ^ 10072643357356766 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 12258406965903184223) ^ 17197082240938 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 12258406965903184223) ^ 1735001446 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_12974279845875135713 : Nat.Prime 12974279845875135713 := by
  apply lucas_primality 12974279845875135713 (3 : ZMod 12974279845875135713)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (28319, 1), (14317110250489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (28319, 1), (14317110250489, 1)] : List FactorBlock).map factorBlockValue).prod) = 12974279845875135713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_28319
      · exact prime_ninetyThreeCM_14317110250489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12974279845875135713) ^ 6487139922937567856 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 12974279845875135713) ^ 458147528015648 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 12974279845875135713) ^ 906208 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_15537358297293529181 : Nat.Prime 15537358297293529181 := by
  apply lucas_primality 15537358297293529181 (3 : ZMod 15537358297293529181)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (109, 1), (2177891, 1), (297503351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (109, 1), (2177891, 1), (297503351, 1)] : List FactorBlock).map factorBlockValue).prod) = 15537358297293529181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_109
      · exact prime_ninetyThreeCM_2177891
      · exact prime_ninetyThreeCM_297503351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15537358297293529181) ^ 7768679148646764590 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 15537358297293529181) ^ 3107471659458705836 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 15537358297293529181) ^ 1412487117935775380 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 15537358297293529181) ^ 142544571534803020 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 15537358297293529181) ^ 7134130356980 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 15537358297293529181) ^ 52225826180 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_16479383100522249469 : Nat.Prime 16479383100522249469 := by
  apply lucas_primality 16479383100522249469 (2 : ZMod 16479383100522249469)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (124843811367592799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (124843811367592799, 1)] : List FactorBlock).map factorBlockValue).prod) = 16479383100522249469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_124843811367592799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16479383100522249469) ^ 8239691550261124734 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16479383100522249469) ^ 5493127700174083156 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16479383100522249469) ^ 1498125736411113588 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 16479383100522249469) ^ 132 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_21352163383882839593 : Nat.Prime 21352163383882839593 := by
  apply lucas_primality 21352163383882839593 (3 : ZMod 21352163383882839593)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (23, 1), (31, 1), (443, 1), (1207148227073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (23, 1), (31, 1), (443, 1), (1207148227073, 1)] : List FactorBlock).map factorBlockValue).prod) = 21352163383882839593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_23
      · exact prime_ninetyThreeCM_31
      · exact prime_ninetyThreeCM_443
      · exact prime_ninetyThreeCM_1207148227073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21352163383882839593) ^ 10676081691941419796 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21352163383882839593) ^ 3050309054840405656 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21352163383882839593) ^ 928354929734036504 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21352163383882839593) ^ 688779463996220632 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21352163383882839593) ^ 48199014410570744 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 21352163383882839593) ^ 17688104 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_26008498000211568287 : Nat.Prime 26008498000211568287 := by
  apply lucas_primality 26008498000211568287 (5 : ZMod 26008498000211568287)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (72649435754780917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (72649435754780917, 1)] : List FactorBlock).map factorBlockValue).prod) = 26008498000211568287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_179
      · exact prime_ninetyThreeCM_72649435754780917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 26008498000211568287) ^ 13004249000105784143 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 26008498000211568287) ^ 145298871509561834 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 26008498000211568287) ^ 358 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_26777329912790129579 : Nat.Prime 26777329912790129579 := by
  apply lucas_primality 26777329912790129579 (6 : ZMod 26777329912790129579)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 2), (23, 1), (233, 1), (599, 1), (679626917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 2), (23, 1), (233, 1), (599, 1), (679626917, 1)] : List FactorBlock).map factorBlockValue).prod) = 26777329912790129579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_23
      · exact prime_ninetyThreeCM_233
      · exact prime_ninetyThreeCM_599
      · exact prime_ninetyThreeCM_679626917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 26777329912790129579) ^ 13388664956395064789 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 26777329912790129579) ^ 1575137053693537034 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 26777329912790129579) ^ 1409333153304743662 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 26777329912790129579) ^ 1164231735338701286 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 26777329912790129579) ^ 114924162715837466 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 26777329912790129579) ^ 44703388836043622 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 26777329912790129579) ^ 39400043234 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_35986177906623500341 : Nat.Prime 35986177906623500341 := by
  apply lucas_primality 35986177906623500341 (6 : ZMod 35986177906623500341)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (599769631777058339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (599769631777058339, 1)] : List FactorBlock).map factorBlockValue).prod) = 35986177906623500341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_599769631777058339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 35986177906623500341) ^ 17993088953311750170 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 35986177906623500341) ^ 11995392635541166780 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 35986177906623500341) ^ 7197235581324700068 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 35986177906623500341) ^ 60 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_36251604949221072283 : Nat.Prime 36251604949221072283 := by
  apply lucas_primality 36251604949221072283 (2 : ZMod 36251604949221072283)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10122491, 1), (596882146717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10122491, 1), (596882146717, 1)] : List FactorBlock).map factorBlockValue).prod) = 36251604949221072283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_10122491
      · exact prime_ninetyThreeCM_596882146717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36251604949221072283) ^ 18125802474610536141 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36251604949221072283) ^ 12083868316407024094 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36251604949221072283) ^ 3581292880302 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 36251604949221072283) ^ 60734946 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_53614911021448867243 : Nat.Prime 53614911021448867243 := by
  apply lucas_primality 53614911021448867243 (2 : ZMod 53614911021448867243)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5279, 1), (20261, 1), (83545257253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5279, 1), (20261, 1), (83545257253, 1)] : List FactorBlock).map factorBlockValue).prod) = 53614911021448867243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5279
      · exact prime_ninetyThreeCM_20261
      · exact prime_ninetyThreeCM_83545257253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53614911021448867243) ^ 26807455510724433621 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 53614911021448867243) ^ 17871637007149622414 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 53614911021448867243) ^ 10156262743218198 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 53614911021448867243) ^ 2646212478231522 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 53614911021448867243) ^ 641746914 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_62525118317319419831 : Nat.Prime 62525118317319419831 := by
  apply lucas_primality 62525118317319419831 (11 : ZMod 62525118317319419831)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (17837, 1), (9473947763807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (17837, 1), (9473947763807, 1)] : List FactorBlock).map factorBlockValue).prod) = 62525118317319419831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_37
      · exact prime_ninetyThreeCM_17837
      · exact prime_ninetyThreeCM_9473947763807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 62525118317319419831) ^ 31262559158659709915 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 62525118317319419831) ^ 12505023663463883966 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 62525118317319419831) ^ 1689868062630254590 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 62525118317319419831) ^ 3505360672608590 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 62525118317319419831) ^ 6599690 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_71148413414584351697 : Nat.Prime 71148413414584351697 := by
  apply lucas_primality 71148413414584351697 (3 : ZMod 71148413414584351697)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1091, 1), (4075871529249791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1091, 1), (4075871529249791, 1)] : List FactorBlock).map factorBlockValue).prod) = 71148413414584351697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_1091
      · exact prime_ninetyThreeCM_4075871529249791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71148413414584351697) ^ 35574206707292175848 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 71148413414584351697) ^ 65213944467996656 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 71148413414584351697) ^ 17456 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_78999579366527528749 : Nat.Prime 78999579366527528749 := by
  apply lucas_primality 78999579366527528749 (7 : ZMod 78999579366527528749)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (2417, 1), (69839685566383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (2417, 1), (69839685566383, 1)] : List FactorBlock).map factorBlockValue).prod) = 78999579366527528749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_2417
      · exact prime_ninetyThreeCM_69839685566383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 78999579366527528749) ^ 39499789683263764374 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 78999579366527528749) ^ 26333193122175842916 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 78999579366527528749) ^ 6076890720502117596 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 78999579366527528749) ^ 32684972845067244 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (7 : ZMod 78999579366527528749) ^ 1131156 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_96154188587635778849 : Nat.Prime 96154188587635778849 := by
  apply lucas_primality 96154188587635778849 (3 : ZMod 96154188587635778849)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (29, 1), (5869, 1), (13313, 1), (1326111953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (29, 1), (5869, 1), (13313, 1), (1326111953, 1)] : List FactorBlock).map factorBlockValue).prod) = 96154188587635778849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_5869
      · exact prime_ninetyThreeCM_13313
      · exact prime_ninetyThreeCM_1326111953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 96154188587635778849) ^ 48077094293817889424 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 96154188587635778849) ^ 3315661675435716512 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 96154188587635778849) ^ 16383402383308192 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 96154188587635778849) ^ 7222578576401696 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 96154188587635778849) ^ 72508349216 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_107504702617642820429 : Nat.Prime 107504702617642820429 := by
  apply lucas_primality 107504702617642820429 (2 : ZMod 107504702617642820429)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1168529376278726309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1168529376278726309, 1)] : List FactorBlock).map factorBlockValue).prod) = 107504702617642820429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_23
      · exact prime_ninetyThreeCM_1168529376278726309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 107504702617642820429) ^ 53752351308821410214 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 107504702617642820429) ^ 4674117505114905236 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 107504702617642820429) ^ 92 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_137806810187491897037 : Nat.Prime 137806810187491897037 := by
  apply lucas_primality 137806810187491897037 (2 : ZMod 137806810187491897037)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (155890056773180879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (155890056773180879, 1)] : List FactorBlock).map factorBlockValue).prod) = 137806810187491897037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_155890056773180879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 137806810187491897037) ^ 68903405093745948518 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 137806810187491897037) ^ 10600523860576299772 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 137806810187491897037) ^ 8106282952205405708 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 137806810187491897037) ^ 884 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_200303246873124288317 : Nat.Prime 200303246873124288317 := by
  apply lucas_primality 200303246873124288317 (2 : ZMod 200303246873124288317)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (641, 1), (1997, 1), (39119374630027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (641, 1), (1997, 1), (39119374630027, 1)] : List FactorBlock).map factorBlockValue).prod) = 200303246873124288317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_641
      · exact prime_ninetyThreeCM_1997
      · exact prime_ninetyThreeCM_39119374630027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 200303246873124288317) ^ 100151623436562144158 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 200303246873124288317) ^ 312485564544655676 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 200303246873124288317) ^ 100302076551389228 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 200303246873124288317) ^ 5120308 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_225951739587025453621 : Nat.Prime 225951739587025453621 := by
  apply lucas_primality 225951739587025453621 (6 : ZMod 225951739587025453621)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (179, 1), (7012779006425371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (179, 1), (7012779006425371, 1)] : List FactorBlock).map factorBlockValue).prod) = 225951739587025453621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_179
      · exact prime_ninetyThreeCM_7012779006425371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 225951739587025453621) ^ 112975869793512726810 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 225951739587025453621) ^ 75317246529008484540 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 225951739587025453621) ^ 45190347917405090724 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 225951739587025453621) ^ 1262300221156566780 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 225951739587025453621) ^ 32220 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_228011219730569859511 : Nat.Prime 228011219730569859511 := by
  apply lucas_primality 228011219730569859511 (12 : ZMod 228011219730569859511)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1669, 1), (4553849006002993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1669, 1), (4553849006002993, 1)] : List FactorBlock).map factorBlockValue).prod) = 228011219730569859511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_1669
      · exact prime_ninetyThreeCM_4553849006002993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 228011219730569859511) ^ 114005609865284929755 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (12 : ZMod 228011219730569859511) ^ 76003739910189953170 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (12 : ZMod 228011219730569859511) ^ 45602243946113971902 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (12 : ZMod 228011219730569859511) ^ 136615470180089790 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (12 : ZMod 228011219730569859511) ^ 50070 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_320579745386772288761 : Nat.Prime 320579745386772288761 := by
  apply lucas_primality 320579745386772288761 (13 : ZMod 320579745386772288761)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (23, 1), (49779463569374579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (23, 1), (49779463569374579, 1)] : List FactorBlock).map factorBlockValue).prod) = 320579745386772288761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_23
      · exact prime_ninetyThreeCM_49779463569374579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 320579745386772288761) ^ 160289872693386144380 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 320579745386772288761) ^ 64115949077354457752 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 320579745386772288761) ^ 45797106483824612680 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 320579745386772288761) ^ 13938249799424882120 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (13 : ZMod 320579745386772288761) ^ 6440 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_411358512714564595559 : Nat.Prime 411358512714564595559 := by
  apply lucas_primality 411358512714564595559 (11 : ZMod 411358512714564595559)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43207, 1), (680046078371171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43207, 1), (680046078371171, 1)] : List FactorBlock).map factorBlockValue).prod) = 411358512714564595559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_43207
      · exact prime_ninetyThreeCM_680046078371171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 411358512714564595559) ^ 205679256357282297779 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 411358512714564595559) ^ 58765501816366370794 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 411358512714564595559) ^ 9520645097196394 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (11 : ZMod 411358512714564595559) ^ 604898 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1079666734764169786943 : Nat.Prime 1079666734764169786943 := by
  apply lucas_primality 1079666734764169786943 (5 : ZMod 1079666734764169786943)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5801, 1), (93058673915201671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5801, 1), (93058673915201671, 1)] : List FactorBlock).map factorBlockValue).prod) = 1079666734764169786943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5801
      · exact prime_ninetyThreeCM_93058673915201671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1079666734764169786943) ^ 539833367382084893471 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079666734764169786943) ^ 186117347830403342 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 1079666734764169786943) ^ 11602 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1990263875915086619431 : Nat.Prime 1990263875915086619431 := by
  apply lucas_primality 1990263875915086619431 (6 : ZMod 1990263875915086619431)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (7346827, 1), (48288974869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (7346827, 1), (48288974869, 1)] : List FactorBlock).map factorBlockValue).prod) = 1990263875915086619431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_7346827
      · exact prime_ninetyThreeCM_48288974869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1990263875915086619431) ^ 995131937957543309715 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1990263875915086619431) ^ 663421291971695539810 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1990263875915086619431) ^ 398052775183017323886 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1990263875915086619431) ^ 180933079628644238130 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1990263875915086619431) ^ 117074345642063918790 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1990263875915086619431) ^ 270901149015090 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 1990263875915086619431) ^ 41215699470 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2400238529353551801041 : Nat.Prime 2400238529353551801041 := by
  apply lucas_primality 2400238529353551801041 (3 : ZMod 2400238529353551801041)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 2), (612305747284069337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 2), (612305747284069337, 1)] : List FactorBlock).map factorBlockValue).prod) = 2400238529353551801041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_612305747284069337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2400238529353551801041) ^ 1200119264676775900520 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2400238529353551801041) ^ 480047705870710360208 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2400238529353551801041) ^ 342891218479078828720 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2400238529353551801041) ^ 3920 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2567851320989378004689 : Nat.Prime 2567851320989378004689 := by
  apply lucas_primality 2567851320989378004689 (3 : ZMod 2567851320989378004689)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (463, 1), (1553, 1), (5189, 1), (43014390583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (463, 1), (1553, 1), (5189, 1), (43014390583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2567851320989378004689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_463
      · exact prime_ninetyThreeCM_1553
      · exact prime_ninetyThreeCM_5189
      · exact prime_ninetyThreeCM_43014390583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2567851320989378004689) ^ 1283925660494689002344 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2567851320989378004689) ^ 5546115164123926576 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2567851320989378004689) ^ 1653477991622265296 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2567851320989378004689) ^ 494864390246555792 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 2567851320989378004689) ^ 59697493936 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_6417051184257376990427 : Nat.Prime 6417051184257376990427 := by
  apply lucas_primality 6417051184257376990427 (2 : ZMod 6417051184257376990427)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (1171, 1), (80789, 1), (181365540121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (1171, 1), (80789, 1), (181365540121, 1)] : List FactorBlock).map factorBlockValue).prod) = 6417051184257376990427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_17
      · exact prime_ninetyThreeCM_1171
      · exact prime_ninetyThreeCM_80789
      · exact prime_ninetyThreeCM_181365540121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6417051184257376990427) ^ 3208525592128688495213 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6417051184257376990427) ^ 583368289477943362766 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6417051184257376990427) ^ 377473599073963352378 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6417051184257376990427) ^ 5479975392192465406 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6417051184257376990427) ^ 79429763758152434 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 6417051184257376990427) ^ 35381865706 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_9503817984232551814313 : Nat.Prime 9503817984232551814313 := by
  apply lucas_primality 9503817984232551814313 (3 : ZMod 9503817984232551814313)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (62525118317319419831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (62525118317319419831, 1)] : List FactorBlock).map factorBlockValue).prod) = 9503817984232551814313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_62525118317319419831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9503817984232551814313) ^ 4751908992116275907156 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9503817984232551814313) ^ 500200946538555358648 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 9503817984232551814313) ^ 152 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_28169751068255216317109 : Nat.Prime 28169751068255216317109 := by
  apply lucas_primality 28169751068255216317109 (2 : ZMod 28169751068255216317109)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (26777329912790129579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (26777329912790129579, 1)] : List FactorBlock).map factorBlockValue).prod) = 28169751068255216317109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_263
      · exact prime_ninetyThreeCM_26777329912790129579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28169751068255216317109) ^ 14084875534127608158554 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28169751068255216317109) ^ 107109319651160518316 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 28169751068255216317109) ^ 1052 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_33100458833530615236019 : Nat.Prime 33100458833530615236019 := by
  apply lucas_primality 33100458833530615236019 (2 : ZMod 33100458833530615236019)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1279, 1), (227017124353803103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1279, 1), (227017124353803103, 1)] : List FactorBlock).map factorBlockValue).prod) = 33100458833530615236019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_19
      · exact prime_ninetyThreeCM_1279
      · exact prime_ninetyThreeCM_227017124353803103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33100458833530615236019) ^ 16550229416765307618009 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33100458833530615236019) ^ 11033486277843538412006 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33100458833530615236019) ^ 1742129412291085012422 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33100458833530615236019) ^ 25879952176333553742 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 33100458833530615236019) ^ 145806 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_75397502144004029452847 : Nat.Prime 75397502144004029452847 := by
  apply lucas_primality 75397502144004029452847 (5 : ZMod 75397502144004029452847)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2381, 1), (3529, 1), (4486585091262427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2381, 1), (3529, 1), (4486585091262427, 1)] : List FactorBlock).map factorBlockValue).prod) = 75397502144004029452847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_2381
      · exact prime_ninetyThreeCM_3529
      · exact prime_ninetyThreeCM_4486585091262427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 75397502144004029452847) ^ 37698751072002014726423 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 75397502144004029452847) ^ 31666317574130209766 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 75397502144004029452847) ^ 21365118204591677374 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 75397502144004029452847) ^ 16805098 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_79784297538106774524187 : Nat.Prime 79784297538106774524187 := by
  apply lucas_primality 79784297538106774524187 (3 : ZMod 79784297538106774524187)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (252667, 1), (434942935312133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (252667, 1), (434942935312133, 1)] : List FactorBlock).map factorBlockValue).prod) = 79784297538106774524187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_252667
      · exact prime_ninetyThreeCM_434942935312133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 79784297538106774524187) ^ 39892148769053387262093 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 79784297538106774524187) ^ 26594765846035591508062 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 79784297538106774524187) ^ 7253117958009706774926 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 79784297538106774524187) ^ 315768571036608558 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 79784297538106774524187) ^ 183436242 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_90712211547683563250201 : Nat.Prime 90712211547683563250201 := by
  apply lucas_primality 90712211547683563250201 (3 : ZMod 90712211547683563250201)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (37, 1), (12258406965903184223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (37, 1), (12258406965903184223, 1)] : List FactorBlock).map factorBlockValue).prod) = 90712211547683563250201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_37
      · exact prime_ninetyThreeCM_12258406965903184223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 90712211547683563250201) ^ 45356105773841781625100 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 90712211547683563250201) ^ 18142442309536712650040 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 90712211547683563250201) ^ 2451681393180636844600 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 90712211547683563250201) ^ 7400 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_94951354716929181307423 : Nat.Prime 94951354716929181307423 := by
  apply lucas_primality 94951354716929181307423 (3 : ZMod 94951354716929181307423)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (3196511, 1), (105335765032661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (3196511, 1), (105335765032661, 1)] : List FactorBlock).map factorBlockValue).prod) = 94951354716929181307423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_47
      · exact prime_ninetyThreeCM_3196511
      · exact prime_ninetyThreeCM_105335765032661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 94951354716929181307423) ^ 47475677358464590653711 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 94951354716929181307423) ^ 31650451572309727102474 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 94951354716929181307423) ^ 2020241589721897474626 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 94951354716929181307423) ^ 29704685739210402 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 94951354716929181307423) ^ 901416102 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_133361174080897272124577 : Nat.Prime 133361174080897272124577 := by
  apply lucas_primality 133361174080897272124577 (3 : ZMod 133361174080897272124577)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (320579745386772288761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (320579745386772288761, 1)] : List FactorBlock).map factorBlockValue).prod) = 133361174080897272124577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_13
      · exact prime_ninetyThreeCM_320579745386772288761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 133361174080897272124577) ^ 66680587040448636062288 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 133361174080897272124577) ^ 10258551852376713240352 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 133361174080897272124577) ^ 416 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_400769896086963991407137 : Nat.Prime 400769896086963991407137 := by
  apply lucas_primality 400769896086963991407137 (3 : ZMod 400769896086963991407137)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (202109543, 1), (61966689285511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (202109543, 1), (61966689285511, 1)] : List FactorBlock).map factorBlockValue).prod) = 400769896086963991407137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_202109543
      · exact prime_ninetyThreeCM_61966689285511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 400769896086963991407137) ^ 200384948043481995703568 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 400769896086963991407137) ^ 1982934057136352 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 400769896086963991407137) ^ 6467505376 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_676021373192755245066259 : Nat.Prime 676021373192755245066259 := by
  apply lucas_primality 676021373192755245066259 (2 : ZMod 676021373192755245066259)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (643, 1), (2543, 1), (8893, 1), (781117, 1), (9919447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (643, 1), (2543, 1), (8893, 1), (781117, 1), (9919447, 1)] : List FactorBlock).map factorBlockValue).prod) = 676021373192755245066259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_643
      · exact prime_ninetyThreeCM_2543
      · exact prime_ninetyThreeCM_8893
      · exact prime_ninetyThreeCM_781117
      · exact prime_ninetyThreeCM_9919447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 676021373192755245066259) ^ 338010686596377622533129 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 676021373192755245066259) ^ 225340457730918415022086 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 676021373192755245066259) ^ 1051355168262449836806 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 676021373192755245066259) ^ 265836167201240757006 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 676021373192755245066259) ^ 76017246507675165306 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 676021373192755245066259) ^ 865454692693610874 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 676021373192755245066259) ^ 68151114995902014 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1629673626334891861009021 : Nat.Prime 1629673626334891861009021 := by
  apply lucas_primality 1629673626334891861009021 (2 : ZMod 1629673626334891861009021)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (359, 1), (10808287745953653409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (359, 1), (10808287745953653409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1629673626334891861009021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_359
      · exact prime_ninetyThreeCM_10808287745953653409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1629673626334891861009021) ^ 814836813167445930504510 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1629673626334891861009021) ^ 543224542111630620336340 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1629673626334891861009021) ^ 325934725266978372201804 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1629673626334891861009021) ^ 232810518047841694429860 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1629673626334891861009021) ^ 4539480853300534431780 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 1629673626334891861009021) ^ 150780 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2082401898135653107548421 : Nat.Prime 2082401898135653107548421 := by
  apply lucas_primality 2082401898135653107548421 (6 : ZMod 2082401898135653107548421)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (127, 1), (983, 1), (278007211591231127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (127, 1), (983, 1), (278007211591231127, 1)] : List FactorBlock).map factorBlockValue).prod) = 2082401898135653107548421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_127
      · exact prime_ninetyThreeCM_983
      · exact prime_ninetyThreeCM_278007211591231127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2082401898135653107548421) ^ 1041200949067826553774210 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2082401898135653107548421) ^ 694133966045217702516140 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2082401898135653107548421) ^ 416480379627130621509684 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2082401898135653107548421) ^ 16396865339650811870460 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2082401898135653107548421) ^ 2118414952325181187740 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 2082401898135653107548421) ^ 7490460 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_6266789411317325966289919 : Nat.Prime 6266789411317325966289919 := by
  apply lucas_primality 6266789411317325966289919 (6 : ZMod 6266789411317325966289919)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (94951354716929181307423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (94951354716929181307423, 1)] : List FactorBlock).map factorBlockValue).prod) = 6266789411317325966289919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_94951354716929181307423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6266789411317325966289919) ^ 3133394705658662983144959 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6266789411317325966289919) ^ 2088929803772441988763306 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6266789411317325966289919) ^ 569708128301575087844538 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 6266789411317325966289919) ^ 66 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_6852653176787939175977353 : Nat.Prime 6852653176787939175977353 := by
  apply lucas_primality 6852653176787939175977353 (5 : ZMod 6852653176787939175977353)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (51283, 1), (350039663, 1), (15905848087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (51283, 1), (350039663, 1), (15905848087, 1)] : List FactorBlock).map factorBlockValue).prod) = 6852653176787939175977353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_51283
      · exact prime_ninetyThreeCM_350039663
      · exact prime_ninetyThreeCM_15905848087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6852653176787939175977353) ^ 3426326588393969587988676 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6852653176787939175977353) ^ 2284217725595979725325784 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6852653176787939175977353) ^ 133624264898464192344 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6852653176787939175977353) ^ 19576790578694904 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 6852653176787939175977353) ^ 430826016903096 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_8879891796281899860972107 : Nat.Prime 8879891796281899860972107 := by
  apply lucas_primality 8879891796281899860972107 (2 : ZMod 8879891796281899860972107)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41227, 1), (1394573611, 1), (11032056107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41227, 1), (1394573611, 1), (11032056107, 1)] : List FactorBlock).map factorBlockValue).prod) = 8879891796281899860972107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_41227
      · exact prime_ninetyThreeCM_1394573611
      · exact prime_ninetyThreeCM_11032056107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8879891796281899860972107) ^ 4439945898140949930486053 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8879891796281899860972107) ^ 1268555970897414265853158 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8879891796281899860972107) ^ 215390200506510293278 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8879891796281899860972107) ^ 6367460079726046 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 8879891796281899860972107) ^ 804917207649758 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_13183551585319242695270579 : Nat.Prime 13183551585319242695270579 := by
  apply lucas_primality 13183551585319242695270579 (2 : ZMod 13183551585319242695270579)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (253447, 1), (26008498000211568287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (253447, 1), (26008498000211568287, 1)] : List FactorBlock).map factorBlockValue).prod) = 13183551585319242695270579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_253447
      · exact prime_ninetyThreeCM_26008498000211568287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13183551585319242695270579) ^ 6591775792659621347635289 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13183551585319242695270579) ^ 52016996000423136574 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 13183551585319242695270579) ^ 506894 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_14081816114441916505962683 : Nat.Prime 14081816114441916505962683 := by
  apply lucas_primality 14081816114441916505962683 (2 : ZMod 14081816114441916505962683)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (240361711, 1), (54346880552329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (240361711, 1), (54346880552329, 1)] : List FactorBlock).map factorBlockValue).prod) = 14081816114441916505962683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_7
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_240361711
      · exact prime_ninetyThreeCM_54346880552329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14081816114441916505962683) ^ 7040908057220958252981341 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14081816114441916505962683) ^ 2011688016348845215137526 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14081816114441916505962683) ^ 1280165101312901500542062 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14081816114441916505962683) ^ 58585937235410662 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 14081816114441916505962683) ^ 259109924458 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_64411728307886633906594393 : Nat.Prime 64411728307886633906594393 := by
  apply lucas_primality 64411728307886633906594393 (3 : ZMod 64411728307886633906594393)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (37, 1), (11083, 1), (677045584661649361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (37, 1), (11083, 1), (677045584661649361, 1)] : List FactorBlock).map factorBlockValue).prod) = 64411728307886633906594393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_29
      · exact prime_ninetyThreeCM_37
      · exact prime_ninetyThreeCM_11083
      · exact prime_ninetyThreeCM_677045584661649361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64411728307886633906594393) ^ 32205864153943316953297196 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 64411728307886633906594393) ^ 2221094079582297720917048 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 64411728307886633906594393) ^ 1740857521834773889367416 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 64411728307886633906594393) ^ 5811759298735598114824 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 64411728307886633906594393) ^ 95136472 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_83044426149216377702837333 : Nat.Prime 83044426149216377702837333 := by
  apply lucas_primality 83044426149216377702837333 (2 : ZMod 83044426149216377702837333)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (67, 1), (28169751068255216317109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (67, 1), (28169751068255216317109, 1)] : List FactorBlock).map factorBlockValue).prod) = 83044426149216377702837333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_67
      · exact prime_ninetyThreeCM_28169751068255216317109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83044426149216377702837333) ^ 41522213074608188851418666 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83044426149216377702837333) ^ 7549493286292397972985212 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83044426149216377702837333) ^ 1239469047003229517952796 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 83044426149216377702837333) ^ 2948 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_133435461433935053493393967 : Nat.Prime 133435461433935053493393967 := by
  apply lucas_primality 133435461433935053493393967 (3 : ZMod 133435461433935053493393967)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (22834517, 1), (539857273, 1), (601350907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (22834517, 1), (539857273, 1), (601350907, 1)] : List FactorBlock).map factorBlockValue).prod) = 133435461433935053493393967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_22834517
      · exact prime_ninetyThreeCM_539857273
      · exact prime_ninetyThreeCM_601350907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 133435461433935053493393967) ^ 66717730716967526746696983 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 133435461433935053493393967) ^ 44478487144645017831131322 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 133435461433935053493393967) ^ 5843585893843738998 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 133435461433935053493393967) ^ 247168035159424542 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 133435461433935053493393967) ^ 221892841402058538 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_228587983828612233011552243 : Nat.Prime 228587983828612233011552243 := by
  apply lucas_primality 228587983828612233011552243 (2 : ZMod 228587983828612233011552243)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (523, 1), (916649, 1), (1248203156071853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (523, 1), (916649, 1), (1248203156071853, 1)] : List FactorBlock).map factorBlockValue).prod) = 228587983828612233011552243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_191
      · exact prime_ninetyThreeCM_523
      · exact prime_ninetyThreeCM_916649
      · exact prime_ninetyThreeCM_1248203156071853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 228587983828612233011552243) ^ 114293991914306116505776121 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 228587983828612233011552243) ^ 1196795726851372947704462 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 228587983828612233011552243) ^ 437070714777461248588054 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 228587983828612233011552243) ^ 249373515738971223458 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 228587983828612233011552243) ^ 183133637114 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_1409625900276442103571238831 : Nat.Prime 1409625900276442103571238831 := by
  apply lucas_primality 1409625900276442103571238831 (3 : ZMod 1409625900276442103571238831)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (997, 1), (12671, 1), (34122887, 1), (109001079469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (997, 1), (12671, 1), (34122887, 1), (109001079469, 1)] : List FactorBlock).map factorBlockValue).prod) = 1409625900276442103571238831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_997
      · exact prime_ninetyThreeCM_12671
      · exact prime_ninetyThreeCM_34122887
      · exact prime_ninetyThreeCM_109001079469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1409625900276442103571238831) ^ 704812950138221051785619415 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1409625900276442103571238831) ^ 469875300092147367857079610 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1409625900276442103571238831) ^ 281925180055288420714247766 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1409625900276442103571238831) ^ 1413867502784796493050390 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1409625900276442103571238831) ^ 111248196691377326459730 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1409625900276442103571238831) ^ 41310276597535317090 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 1409625900276442103571238831) ^ 12932219636204070 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_2243894290235969062827686303 : Nat.Prime 2243894290235969062827686303 := by
  apply lucas_primality 2243894290235969062827686303 (5 : ZMod 2243894290235969062827686303)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (631, 1), (727, 1), (3877, 1), (60813239, 1), (241238287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (631, 1), (727, 1), (3877, 1), (60813239, 1), (241238287, 1)] : List FactorBlock).map factorBlockValue).prod) = 2243894290235969062827686303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_43
      · exact prime_ninetyThreeCM_631
      · exact prime_ninetyThreeCM_727
      · exact prime_ninetyThreeCM_3877
      · exact prime_ninetyThreeCM_60813239
      · exact prime_ninetyThreeCM_241238287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2243894290235969062827686303) ^ 1121947145117984531413843151 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2243894290235969062827686303) ^ 52183588145022536344829914 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2243894290235969062827686303) ^ 3556092377553041304005842 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2243894290235969062827686303) ^ 3086512091108623195086226 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2243894290235969062827686303) ^ 578770773855034579011526 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2243894290235969062827686303) ^ 36898121644794632018 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (5 : ZMod 2243894290235969062827686303) ^ 9301567832124297346 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_4780470444415760177328549079 : Nat.Prime 4780470444415760177328549079 := by
  apply lucas_primality 4780470444415760177328549079 (6 : ZMod 4780470444415760177328549079)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5003, 1), (1879921, 1), (4507339, 1), (6264808603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5003, 1), (1879921, 1), (4507339, 1), (6264808603, 1)] : List FactorBlock).map factorBlockValue).prod) = 4780470444415760177328549079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5003
      · exact prime_ninetyThreeCM_1879921
      · exact prime_ninetyThreeCM_4507339
      · exact prime_ninetyThreeCM_6264808603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4780470444415760177328549079) ^ 2390235222207880088664274539 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 4780470444415760177328549079) ^ 1593490148138586725776183026 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 4780470444415760177328549079) ^ 955520776417301654473026 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 4780470444415760177328549079) ^ 2542910284217134750518 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 4780470444415760177328549079) ^ 1060597049482135729602 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (6 : ZMod 4780470444415760177328549079) ^ 763067277446681826 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_5786885274819078109397717309 : Nat.Prime 5786885274819078109397717309 := by
  apply lucas_primality 5786885274819078109397717309 (2 : ZMod 5786885274819078109397717309)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (359, 1), (12517, 1), (1461139, 1), (3396551, 1), (64872481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (359, 1), (12517, 1), (1461139, 1), (3396551, 1), (64872481, 1)] : List FactorBlock).map factorBlockValue).prod) = 5786885274819078109397717309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_359
      · exact prime_ninetyThreeCM_12517
      · exact prime_ninetyThreeCM_1461139
      · exact prime_ninetyThreeCM_3396551
      · exact prime_ninetyThreeCM_64872481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5786885274819078109397717309) ^ 2893442637409539054698858654 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5786885274819078109397717309) ^ 16119457590025287212807012 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5786885274819078109397717309) ^ 462322063978515467715724 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5786885274819078109397717309) ^ 3960530295077386962772 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5786885274819078109397717309) ^ 1703753388310400199908 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 5786885274819078109397717309) ^ 89204007394430900668 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_7330054681437498938570441921 : Nat.Prime 7330054681437498938570441921 := by
  apply lucas_primality 7330054681437498938570441921 (3 : ZMod 7330054681437498938570441921)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (11, 1), (2082401898135653107548421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (11, 1), (2082401898135653107548421, 1)] : List FactorBlock).map factorBlockValue).prod) = 7330054681437498938570441921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_11
      · exact prime_ninetyThreeCM_2082401898135653107548421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7330054681437498938570441921) ^ 3665027340718749469285220960 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7330054681437498938570441921) ^ 1466010936287499787714088384 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7330054681437498938570441921) ^ 666368607403408994415494720 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7330054681437498938570441921) ^ 3520 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_7330054681437498938570441923 : Nat.Prime 7330054681437498938570441923 := by
  apply lucas_primality 7330054681437498938570441923 (3 : ZMod 7330054681437498938570441923)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1619, 1), (9839, 1), (660160573, 1), (38724633553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1619, 1), (9839, 1), (660160573, 1), (38724633553, 1)] : List FactorBlock).map factorBlockValue).prod) = 7330054681437498938570441923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_1619
      · exact prime_ninetyThreeCM_9839
      · exact prime_ninetyThreeCM_660160573
      · exact prime_ninetyThreeCM_38724633553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7330054681437498938570441923) ^ 3665027340718749469285220961 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7330054681437498938570441923) ^ 2443351560479166312856813974 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7330054681437498938570441923) ^ 4527519877354848016411638 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7330054681437498938570441923) ^ 744999967622471688034398 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7330054681437498938570441923) ^ 11103442073384014314 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 7330054681437498938570441923) ^ 189286611877303074 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_15707260031651783439793804123 : Nat.Prime 15707260031651783439793804123 := by
  apply lucas_primality 15707260031651783439793804123 (2 : ZMod 15707260031651783439793804123)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (34721, 1), (75397502144004029452847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (34721, 1), (75397502144004029452847, 1)] : List FactorBlock).map factorBlockValue).prod) = 15707260031651783439793804123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_34721
      · exact prime_ninetyThreeCM_75397502144004029452847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15707260031651783439793804123) ^ 7853630015825891719896902061 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15707260031651783439793804123) ^ 5235753343883927813264601374 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15707260031651783439793804123) ^ 452385012864024176717082 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (2 : ZMod 15707260031651783439793804123) ^ 208326 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem prime_ninetyThreeCM_54975410110781242039278314431 : Nat.Prime 54975410110781242039278314431 := by
  apply lucas_primality 54975410110781242039278314431 (3 : ZMod 54975410110781242039278314431)
  · rw [← ninetyThreeCMFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (139, 1), (13183551585319242695270579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (139, 1), (13183551585319242695270579, 1)] : List FactorBlock).map factorBlockValue).prod) = 54975410110781242039278314431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_ninetyThreeCM_2
      · exact prime_ninetyThreeCM_3
      · exact prime_ninetyThreeCM_5
      · exact prime_ninetyThreeCM_139
      · exact prime_ninetyThreeCM_13183551585319242695270579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 54975410110781242039278314431) ^ 27487705055390621019639157215 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 54975410110781242039278314431) ^ 18325136703593747346426104810 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 54975410110781242039278314431) ^ 10995082022156248407855662886 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 54975410110781242039278314431) ^ 395506547559577280858117370 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide
    · change (3 : ZMod 54975410110781242039278314431) ^ 4170 ≠ 1
      rw [← ninetyThreeCMFastPow_eq_pow]
      decide

private theorem phi_ninetyThreeCM_109950820221562484078556628793 : Nat.totient 109950820221562484078556628793 = 109935379837184291935651452160 := by
  rw [← show ((([(7121, 1), (4988360717, 1), (3095277830883149, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628793 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_7121, prime_ninetyThreeCM_4988360717, prime_ninetyThreeCM_3095277830883149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628794 : Nat.totient 109950820221562484078556628794 = 35049749680659474635941946880 := by
  rw [← show ((([(2, 1), (3, 2), (23, 1), (5003, 1), (1879921, 1), (4507339, 1), (6264808603, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628794 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_23, prime_ninetyThreeCM_5003, prime_ninetyThreeCM_1879921, prime_ninetyThreeCM_4507339, prime_ninetyThreeCM_6264808603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628795 : Nat.totient 109950820221562484078556628795 = 78429315137728604582410536960 := by
  rw [← show ((([(5, 1), (17, 1), (19, 1), (317540261, 1), (426790687, 1), (502356719, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628795 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_5, prime_ninetyThreeCM_17, prime_ninetyThreeCM_19, prime_ninetyThreeCM_317540261, prime_ninetyThreeCM_426790687, prime_ninetyThreeCM_502356719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628796 : Nat.totient 109950820221562484078556628796 = 54124975223304755940984880512 := by
  rw [← show ((([(2, 2), (73, 1), (557, 1), (676021373192755245066259, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628796 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_73, prime_ninetyThreeCM_557, prime_ninetyThreeCM_676021373192755245066259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628797 : Nat.totient 109950820221562484078556628797 = 70760062969572896838870336000 := by
  rw [← show ((([(3, 1), (29, 1), (5501, 1), (5314783, 1), (43226695692678457, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628797 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_29, prime_ninetyThreeCM_5501, prime_ninetyThreeCM_5314783, prime_ninetyThreeCM_43226695692678457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628798 : Nat.totient 109950820221562484078556628798 = 45877937086645247271724565760 := by
  rw [← show ((([(2, 1), (7, 2), (43, 1), (631, 1), (727, 1), (3877, 1), (60813239, 1), (241238287, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628798 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_7, prime_ninetyThreeCM_43, prime_ninetyThreeCM_631, prime_ninetyThreeCM_727, prime_ninetyThreeCM_3877, prime_ninetyThreeCM_60813239, prime_ninetyThreeCM_241238287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628799 : Nat.totient 109950820221562484078556628799 = 109950820221443257103866232040 := by
  rw [← show ((([(922204651829, 1), (119226052485744931, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628799 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_922204651829, prime_ninetyThreeCM_119226052485744931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628800 : Nat.totient 109950820221562484078556628800 = 26654744296136359776619776000 := by
  rw [← show ((([(2, 6), (3, 1), (5, 2), (11, 1), (2082401898135653107548421, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_5, prime_ninetyThreeCM_11, prime_ninetyThreeCM_2082401898135653107548421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628801 : Nat.totient 109950820221562484078556628801 = 109763496866833756752416163840 := by
  rw [← show ((([(587, 1), (10907089, 1), (30952531, 1), (554824139297, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_587, prime_ninetyThreeCM_10907089, prime_ninetyThreeCM_30952531, prime_ninetyThreeCM_554824139297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628802 : Nat.totient 109950820221562484078556628802 = 54965549801202772582597253760 := by
  rw [← show ((([(2, 1), (5581, 1), (5579773, 1), (1765387000332731977, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_5581, prime_ninetyThreeCM_5579773, prime_ninetyThreeCM_1765387000332731977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628803 : Nat.totient 109950820221562484078556628803 = 69113717208901865658888576000 := by
  rw [← show ((([(3, 4), (31, 1), (61, 1), (107, 1), (9437, 1), (117231467, 1), (6064011181, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_31, prime_ninetyThreeCM_61, prime_ninetyThreeCM_107, prime_ninetyThreeCM_9437, prime_ninetyThreeCM_117231467, prime_ninetyThreeCM_6064011181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628804 : Nat.totient 109950820221562484078556628804 = 54975410108812535533026076008 := by
  rw [← show ((([(2, 2), (27924635539, 1), (984353225201483659, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_27924635539, prime_ninetyThreeCM_984353225201483659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628805 : Nat.totient 109950820221562484078556628805 = 69595221696055198295507926272 := by
  rw [← show ((([(5, 1), (7, 1), (13, 1), (3058879, 1), (78999579366527528749, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_5, prime_ninetyThreeCM_7, prime_ninetyThreeCM_13, prime_ninetyThreeCM_3058879, prime_ninetyThreeCM_78999579366527528749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628806 : Nat.totient 109950820221562484078556628806 = 36311238562785502202213437440 := by
  rw [← show ((([(2, 1), (3, 1), (109, 1), (16561, 1), (60413, 1), (168036553526914873, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_109, prime_ninetyThreeCM_16561, prime_ninetyThreeCM_60413, prime_ninetyThreeCM_168036553526914873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628807 : Nat.totient 109950820221562484078556628807 = 109950820221455878913215683480 := by
  rw [← show ((([(1031393588131, 1), (106604133947357197, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_1031393588131, prime_ninetyThreeCM_106604133947357197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628808 : Nat.totient 109950820221562484078556628808 = 54441668265045501825304738128 := by
  rw [← show ((([(2, 3), (103, 1), (133435461433935053493393967, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_103, prime_ninetyThreeCM_133435461433935053493393967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628809 : Nat.totient 109950820221562484078556628809 = 71319272984366926895133599232 := by
  rw [← show ((([(3, 1), (37, 1), (402107, 1), (117728189, 1), (20924418513353, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_37, prime_ninetyThreeCM_402107, prime_ninetyThreeCM_117728189, prime_ninetyThreeCM_20924418513353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628810 : Nat.totient 109950820221562484078556628810 = 42724676685882897870864261120 := by
  rw [← show ((([(2, 1), (5, 1), (47, 1), (137, 1), (7489, 1), (228011219730569859511, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_5, prime_ninetyThreeCM_47, prime_ninetyThreeCM_137, prime_ninetyThreeCM_7489, prime_ninetyThreeCM_228011219730569859511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628811 : Nat.totient 109950820221562484078556628811 = 99955290399027215015075806720 := by
  rw [← show ((([(11, 1), (140488433, 1), (71148413414584351697, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_11, prime_ninetyThreeCM_140488433, prime_ninetyThreeCM_71148413414584351697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628812 : Nat.totient 109950820221562484078556628812 = 29503510156416916351879741440 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (17, 1), (883, 1), (1321, 1), (4337, 1), (65327, 1), (77661067049, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_7, prime_ninetyThreeCM_17, prime_ninetyThreeCM_883, prime_ninetyThreeCM_1321, prime_ninetyThreeCM_4337, prime_ninetyThreeCM_65327, prime_ninetyThreeCM_77661067049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628813 : Nat.totient 109950820221562484078556628813 = 109950419451666397114564947328 := by
  rw [← show ((([(274349, 1), (400769896086963991407137, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_274349, prime_ninetyThreeCM_400769896086963991407137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628814 : Nat.totient 109950820221562484078556628814 = 52081964992849119609347374464 := by
  rw [← show ((([(2, 1), (19, 1), (20996369, 1), (137806810187491897037, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_19, prime_ninetyThreeCM_20996369, prime_ninetyThreeCM_137806810187491897037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628815 : Nat.totient 109950820221562484078556628815 = 58640437451499991508563535360 := by
  rw [← show ((([(3, 1), (5, 1), (7330054681437498938570441921, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_5, prime_ninetyThreeCM_7330054681437498938570441921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628816 : Nat.totient 109950820221562484078556628816 = 54798640302635505171756706560 := by
  rw [← show ((([(2, 4), (311, 1), (76600515707, 1), (288460537436713, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_311, prime_ninetyThreeCM_76600515707, prime_ninetyThreeCM_288460537436713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628817 : Nat.totient 109950820221562484078556628817 = 105170349777146723901228079716 := by
  rw [← show ((([(23, 1), (4780470444415760177328549079, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_23, prime_ninetyThreeCM_4780470444415760177328549079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628818 : Nat.totient 109950820221562484078556628818 = 33831021606634610485709731920 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (1409625900276442103571238831, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_13, prime_ninetyThreeCM_1409625900276442103571238831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628819 : Nat.totient 109950820221562484078556628819 = 94033125204204239977224720384 := by
  rw [← show ((([(7, 1), (449, 1), (174649, 1), (200303246873124288317, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_7, prime_ninetyThreeCM_449, prime_ninetyThreeCM_174649, prime_ninetyThreeCM_200303246873124288317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628820 : Nat.totient 109950820221562484078556628820 = 43980319451291115518023620896 := by
  rw [← show ((([(2, 2), (5, 1), (5091887, 1), (1079666734764169786943, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_5, prime_ninetyThreeCM_5091887, prime_ninetyThreeCM_1079666734764169786943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628821 : Nat.totient 109950820221562484078556628821 = 73300400484281951634420734016 := by
  rw [← show ((([(3, 2), (502643, 1), (146642569, 1), (165743408162407, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_502643, prime_ninetyThreeCM_146642569, prime_ninetyThreeCM_165743408162407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628822 : Nat.totient 109950820221562484078556628822 = 49007699033225726269666270080 := by
  rw [← show ((([(2, 1), (11, 1), (53, 1), (3229, 1), (4159, 1), (7021711111818577247, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_11, prime_ninetyThreeCM_53, prime_ninetyThreeCM_3229, prime_ninetyThreeCM_4159, prime_ninetyThreeCM_7021711111818577247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628823 : Nat.totient 109950820221562484078556628823 = 109950820114057781459891054808 := by
  rw [← show ((([(1022753587, 1), (107504702617642820429, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_1022753587, prime_ninetyThreeCM_107504702617642820429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628824 : Nat.totient 109950820221562484078556628824 = 36650269750816557606178961280 := by
  rw [← show ((([(2, 3), (3, 1), (10033091, 1), (20800054549, 1), (21952703239, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_10033091, prime_ninetyThreeCM_20800054549, prime_ninetyThreeCM_21952703239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628825 : Nat.totient 109950820221562484078556628825 = 87960655866502821311313483200 := by
  rw [← show ((([(5, 2), (283061813, 1), (15537358297293529181, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_5, prime_ninetyThreeCM_283061813, prime_ninetyThreeCM_15537358297293529181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628826 : Nat.totient 109950820221562484078556628826 = 45435629844698293628210791680 := by
  rw [← show ((([(2, 1), (7, 1), (29, 1), (743, 1), (1667837, 1), (218539538681504981, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_7, prime_ninetyThreeCM_29, prime_ninetyThreeCM_743, prime_ninetyThreeCM_1667837, prime_ninetyThreeCM_218539538681504981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628827 : Nat.totient 109950820221562484078556628827 = 73300227791326279401683351040 := by
  rw [← show ((([(3, 1), (255971, 1), (4475837, 1), (4504369, 1), (7101960143, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_255971, prime_ninetyThreeCM_4475837, prime_ninetyThreeCM_4504369, prime_ninetyThreeCM_7101960143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628828 : Nat.totient 109950820221562484078556628828 = 54105164394318409785499464000 := by
  rw [← show ((([(2, 2), (101, 1), (167, 1), (1629673626334891861009021, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_101, prime_ninetyThreeCM_167, prime_ninetyThreeCM_1629673626334891861009021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628829 : Nat.totient 109950820221562484078556628829 = 103470098498334171144347000832 := by
  rw [← show ((([(17, 1), (7993, 1), (1303013, 1), (506471549, 1), (1226128357, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_17, prime_ninetyThreeCM_7993, prime_ninetyThreeCM_1303013, prime_ninetyThreeCM_506471549, prime_ninetyThreeCM_1226128357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628830 : Nat.totient 109950820221562484078556628830 = 29299130441873952250350938112 := by
  rw [← show ((([(2, 1), (3, 3), (5, 1), (1619, 1), (9839, 1), (660160573, 1), (38724633553, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_5, prime_ninetyThreeCM_1619, prime_ninetyThreeCM_9839, prime_ninetyThreeCM_660160573, prime_ninetyThreeCM_38724633553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628831 : Nat.totient 109950820221562484078556628831 = 101333525879739483395996958720 := by
  rw [← show ((([(13, 1), (643, 1), (59753, 1), (13355729521, 1), (16482262193, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_13, prime_ninetyThreeCM_643, prime_ninetyThreeCM_59753, prime_ninetyThreeCM_13355729521, prime_ninetyThreeCM_16482262193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628832 : Nat.totient 109950820221562484078556628832 = 54525288520462031573800794624 := by
  rw [← show ((([(2, 5), (127, 1), (3163, 1), (129527533, 1), (66036415028347, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_127, prime_ninetyThreeCM_3163, prime_ninetyThreeCM_129527533, prime_ninetyThreeCM_66036415028347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628833 : Nat.totient 109950820221562484078556628833 = 52619392456993426079138112000 := by
  rw [← show ((([(3, 1), (7, 1), (11, 1), (19, 1), (41, 1), (307, 1), (1990263875915086619431, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_7, prime_ninetyThreeCM_11, prime_ninetyThreeCM_19, prime_ninetyThreeCM_41, prime_ninetyThreeCM_307, prime_ninetyThreeCM_1990263875915086619431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628834 : Nat.totient 109950820221562484078556628834 = 53202009395398613044753399680 := by
  rw [← show ((([(2, 1), (31, 1), (136685839, 1), (12974279845875135713, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_31, prime_ninetyThreeCM_136685839, prime_ninetyThreeCM_12974279845875135713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628835 : Nat.totient 109950820221562484078556628835 = 87660397835470735853868218368 := by
  rw [← show ((([(5, 1), (293, 1), (1826519, 1), (26317517, 1), (1561319351153, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_5, prime_ninetyThreeCM_293, prime_ninetyThreeCM_1826519, prime_ninetyThreeCM_26317517, prime_ninetyThreeCM_1561319351153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628836 : Nat.totient 109950820221562484078556628836 = 36650273378621728848772169472 := by
  rw [← show ((([(2, 2), (3, 1), (1283013857, 1), (7141441459736996179, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_1283013857, prime_ninetyThreeCM_7141441459736996179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628837 : Nat.totient 109950820221562484078556628837 = 108559037687102251814234486544 := by
  rw [← show ((([(79, 1), (11866082938319, 1), (117290814642437, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_79, prime_ninetyThreeCM_11866082938319, prime_ninetyThreeCM_117290814642437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628838 : Nat.totient 109950820221562484078556628838 = 54139586029148760772883328000 := by
  rw [← show ((([(2, 1), (71, 1), (881, 1), (197868361, 1), (4441788386936029, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_71, prime_ninetyThreeCM_881, prime_ninetyThreeCM_197868361, prime_ninetyThreeCM_4441788386936029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628839 : Nat.totient 109950820221562484078556628839 = 73300546492685523255644048592 := by
  rw [← show ((([(3, 2), (227861197, 1), (53614911021448867243, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_227861197, prime_ninetyThreeCM_53614911021448867243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628840 : Nat.totient 109950820221562484078556628840 = 35010892680759639315018547200 := by
  rw [← show ((([(2, 3), (5, 1), (7, 1), (23, 1), (59, 1), (131, 1), (337, 1), (683, 1), (3491, 1), (2749089287369, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_5, prime_ninetyThreeCM_7, prime_ninetyThreeCM_23, prime_ninetyThreeCM_59, prime_ninetyThreeCM_131, prime_ninetyThreeCM_337, prime_ninetyThreeCM_683, prime_ninetyThreeCM_3491, prime_ninetyThreeCM_2749089287369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628841 : Nat.totient 109950820221562484078556628841 = 104700299016535641203838197760 := by
  rw [← show ((([(43, 1), (67, 1), (97, 1), (61074289, 1), (77740511, 1), (82866247, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_43, prime_ninetyThreeCM_67, prime_ninetyThreeCM_97, prime_ninetyThreeCM_61074289, prime_ninetyThreeCM_77740511, prime_ninetyThreeCM_82866247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628842 : Nat.totient 109950820221562484078556628842 = 36650273214879117517199490432 := by
  rw [← show ((([(2, 1), (3, 1), (190580743, 1), (96154188587635778849, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_190580743, prime_ninetyThreeCM_96154188587635778849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628843 : Nat.totient 109950820221562484078556628843 = 109950686860388403181283679808 := by
  rw [← show ((([(824459, 1), (133361174080897272124577, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_824459, prime_ninetyThreeCM_133361174080897272124577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628844 : Nat.totient 109950820221562484078556628844 = 46133211260605383285846699840 := by
  rw [← show ((([(2, 2), (11, 1), (13, 1), (2179272803, 1), (88204520980322759, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_11, prime_ninetyThreeCM_13, prime_ninetyThreeCM_2179272803, prime_ninetyThreeCM_88204520980322759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628845 : Nat.totient 109950820221562484078556628845 = 58640437451499991508563535376 := by
  rw [← show ((([(3, 1), (5, 1), (7330054681437498938570441923, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_5, prime_ninetyThreeCM_7330054681437498938570441923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628846 : Nat.totient 109950820221562484078556628846 = 50343141789000540737204682240 := by
  rw [← show ((([(2, 1), (17, 1), (37, 1), (821877541, 1), (106343443608552607, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_17, prime_ninetyThreeCM_37, prime_ninetyThreeCM_821877541, prime_ninetyThreeCM_106343443608552607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628847 : Nat.totient 109950820221562484078556628847 = 94243560189910700638762824684 := by
  rw [← show ((([(7, 2), (2243894290235969062827686303, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_7, prime_ninetyThreeCM_2243894290235969062827686303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628848 : Nat.totient 109950820221562484078556628848 = 36504000155700244691916672000 := by
  rw [← show ((([(2, 4), (3, 2), (251, 1), (142469, 1), (21352163383882839593, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_251, prime_ninetyThreeCM_142469, prime_ninetyThreeCM_21352163383882839593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628849 : Nat.totient 109950820221562484078556628849 = 109899855956868720113119338240 := by
  rw [← show ((([(2437, 1), (18797, 1), (2400238529353551801041, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2437, prime_ninetyThreeCM_18797, prime_ninetyThreeCM_2400238529353551801041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628850 : Nat.totient 109950820221562484078556628850 = 43980328088622936381035103120 := by
  rw [← show ((([(2, 1), (5, 2), (30308805552499, 1), (72553713824923, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_5, prime_ninetyThreeCM_30308805552499, prime_ninetyThreeCM_72553713824923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628851 : Nat.totient 109950820221562484078556628851 = 73171723357759216117891229312 := by
  rw [← show ((([(3, 1), (569, 1), (64411728307886633906594393, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_569, prime_ninetyThreeCM_64411728307886633906594393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628852 : Nat.totient 109950820221562484078556628852 = 51932691413717643485784576000 := by
  rw [← show ((([(2, 2), (19, 1), (359, 1), (12517, 1), (1461139, 1), (3396551, 1), (64872481, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_19, prime_ninetyThreeCM_359, prime_ninetyThreeCM_12517, prime_ninetyThreeCM_1461139, prime_ninetyThreeCM_3396551, prime_ninetyThreeCM_64872481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628853 : Nat.totient 109950820221562484078556628853 = 109950820185310879126302564780 := by
  rw [← show ((([(3032991791, 1), (36251604949221072283, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3032991791, prime_ninetyThreeCM_36251604949221072283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628854 : Nat.totient 109950820221562484078556628854 = 31413615293277838831233757440 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (34721, 1), (75397502144004029452847, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_7, prime_ninetyThreeCM_34721, prime_ninetyThreeCM_75397502144004029452847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628855 : Nat.totient 109950820221562484078556628855 = 77206845547429455904691789760 := by
  rw [← show ((([(5, 1), (11, 2), (29, 1), (6266789411317325966289919, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_5, prime_ninetyThreeCM_11, prime_ninetyThreeCM_29, prime_ninetyThreeCM_6266789411317325966289919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628856 : Nat.totient 109950820221562484078556628856 = 54973751364637280499368563200 := by
  rw [← show ((([(2, 3), (33317, 1), (9319333, 1), (19978837, 1), (2215580651, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_33317, prime_ninetyThreeCM_9319333, prime_ninetyThreeCM_19978837, prime_ninetyThreeCM_2215580651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628857 : Nat.totient 109950820221562484078556628857 = 66222425267624505838843444032 := by
  rw [← show ((([(3, 3), (13, 1), (47, 1), (13414239347, 1), (496852464104723, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_13, prime_ninetyThreeCM_47, prime_ninetyThreeCM_13414239347, prime_ninetyThreeCM_496852464104723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628858 : Nat.totient 109950820221562484078556628858 = 54974685831043130198902071216 := by
  rw [← show ((([(2, 1), (77659, 1), (3451963, 1), (133948123, 1), (1530995519, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_77659, prime_ninetyThreeCM_3451963, prime_ninetyThreeCM_133948123, prime_ninetyThreeCM_1530995519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628859 : Nat.totient 109950820221562484078556628859 = 109676628649570149586945926400 := by
  rw [← show ((([(401, 1), (298544622377, 1), (918427434538067, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_401, prime_ninetyThreeCM_298544622377, prime_ninetyThreeCM_918427434538067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628860 : Nat.totient 109950820221562484078556628860 = 29109281900384887871157436224 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (139, 1), (13183551585319242695270579, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_5, prime_ninetyThreeCM_139, prime_ninetyThreeCM_13183551585319242695270579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628861 : Nat.totient 109950820221562484078556628861 = 94243560189910700638762824732 := by
  rw [← show ((([(7, 1), (15707260031651783439793804123, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_7, prime_ninetyThreeCM_15707260031651783439793804123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628862 : Nat.totient 109950820221562484078556628862 = 54975410110781242039278314430 := by
  rw [← show ((([(2, 1), (54975410110781242039278314431, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_54975410110781242039278314431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628863 : Nat.totient 109950820221562484078556628863 = 65989227474371065166357485056 := by
  rw [← show ((([(3, 1), (17, 1), (23, 1), (5687999, 1), (16479383100522249469, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_17, prime_ninetyThreeCM_23, prime_ninetyThreeCM_5687999, prime_ninetyThreeCM_16479383100522249469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628864 : Nat.totient 109950820221562484078556628864 = 54074173879456959382896698880 := by
  rw [← show ((([(2, 7), (61, 1), (14081816114441916505962683, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_61, prime_ninetyThreeCM_14081816114441916505962683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628865 : Nat.totient 109950820221562484078556628865 = 85123215655389077227715660160 := by
  rw [← show ((([(5, 1), (31, 1), (6365599255817, 1), (111436504554299, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_5, prime_ninetyThreeCM_31, prime_ninetyThreeCM_6365599255817, prime_ninetyThreeCM_111436504554299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628866 : Nat.totient 109950820221562484078556628866 = 33312509050555292188750646400 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (5813, 1), (175691, 1), (543730187669760349, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_11, prime_ninetyThreeCM_5813, prime_ninetyThreeCM_175691, prime_ninetyThreeCM_543730187669760349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628867 : Nat.totient 109950820221562484078556628867 = 109950820221237783955263066096 := by
  rw [← show ((([(338623015513, 1), (324699784670547259, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_338623015513, prime_ninetyThreeCM_324699784670547259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628868 : Nat.totient 109950820221562484078556628868 = 47121779663121215438589967200 := by
  rw [← show ((([(2, 2), (7, 1), (109120091, 1), (35986177906623500341, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_7, prime_ninetyThreeCM_109120091, prime_ninetyThreeCM_35986177906623500341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628869 : Nat.totient 109950820221562484078556628869 = 72296370499100186030888491776 := by
  rw [← show ((([(3, 1), (73, 1), (1220489, 1), (411358512714564595559, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_73, prime_ninetyThreeCM_1220489, prime_ninetyThreeCM_411358512714564595559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628870 : Nat.totient 109950820221562484078556628870 = 40597214929605151757396352000 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (3727753, 1), (376759751, 1), (602203799933, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_5, prime_ninetyThreeCM_13, prime_ninetyThreeCM_3727753, prime_ninetyThreeCM_376759751, prime_ninetyThreeCM_602203799933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628871 : Nat.totient 109950820221562484078556628871 = 104163934946743405969158911544 := by
  rw [← show ((([(19, 1), (5786885274819078109397717309, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_19, prime_ninetyThreeCM_5786885274819078109397717309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628872 : Nat.totient 109950820221562484078556628872 = 36650255582504976036441134400 := by
  rw [← show ((([(2, 3), (3, 1), (2467351, 1), (12337727, 1), (150494677223939, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_2467351, prime_ninetyThreeCM_12337727, prime_ninetyThreeCM_150494677223939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628873 : Nat.totient 109950820221562484078556628873 = 108625332231119554309554779424 := by
  rw [← show ((([(83, 1), (139387, 1), (9503817984232551814313, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_83, prime_ninetyThreeCM_139387, prime_ninetyThreeCM_9503817984232551814313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628874 : Nat.totient 109950820221562484078556628874 = 53279350777691399165832636000 := by
  rw [← show ((([(2, 1), (41, 1), (151, 1), (8879891796281899860972107, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_41, prime_ninetyThreeCM_151, prime_ninetyThreeCM_8879891796281899860972107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628875 : Nat.totient 109950820221562484078556628875 = 49190239807612986221568000000 := by
  rw [← show ((([(3, 2), (5, 3), (7, 1), (53, 1), (419, 1), (7537, 1), (196751, 1), (513053, 1), (826381, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_5, prime_ninetyThreeCM_7, prime_ninetyThreeCM_53, prime_ninetyThreeCM_419, prime_ninetyThreeCM_7537, prime_ninetyThreeCM_196751, prime_ninetyThreeCM_513053, prime_ninetyThreeCM_826381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628876 : Nat.totient 109950820221562484078556628876 = 54696347115285487886604238272 := by
  rw [← show ((([(2, 2), (197, 1), (9187067985853, 1), (15187815955859, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_197, prime_ninetyThreeCM_9187067985853, prime_ninetyThreeCM_15187815955859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628877 : Nat.totient 109950820221562484078556628877 = 99715453944287618692512691200 := by
  rw [← show ((([(11, 1), (439, 1), (8209, 1), (15361318597, 1), (180560403181, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_11, prime_ninetyThreeCM_439, prime_ninetyThreeCM_8209, prime_ninetyThreeCM_15361318597, prime_ninetyThreeCM_180560403181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628878 : Nat.totient 109950820221562484078556628878 = 36650273407186940894395138560 := by
  rw [← show ((([(2, 1), (3, 1), (109412414208193, 1), (167486814327341, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_109412414208193, prime_ninetyThreeCM_167486814327341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628879 : Nat.totient 109950820221562484078556628879 = 108715417507244134850517974016 := by
  rw [← show ((([(89, 1), (453134273, 1), (2726349667220114407, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_89, prime_ninetyThreeCM_453134273, prime_ninetyThreeCM_2726349667220114407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628880 : Nat.totient 109950820221562484078556628880 = 41393249907507997401911377920 := by
  rw [← show ((([(2, 4), (5, 1), (17, 1), (710531981, 1), (113782621333386793, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_5, prime_ninetyThreeCM_17, prime_ninetyThreeCM_710531981, prime_ninetyThreeCM_113782621333386793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628881 : Nat.totient 109950820221562484078556628881 = 72651865443292914505057868544 := by
  rw [← show ((([(3, 1), (113, 1), (18886499, 1), (625022623, 1), (27475877927, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_113, prime_ninetyThreeCM_18886499, prime_ninetyThreeCM_625022623, prime_ninetyThreeCM_27475877927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628882 : Nat.totient 109950820221562484078556628882 = 46972660659535577392870549776 := by
  rw [← show ((([(2, 1), (7, 1), (347, 1), (3527, 1), (6417051184257376990427, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_7, prime_ninetyThreeCM_347, prime_ninetyThreeCM_3527, prime_ninetyThreeCM_6417051184257376990427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628883 : Nat.totient 109950820221562484078556628883 = 98750009013960484660990568544 := by
  rw [← show ((([(13, 1), (37, 1), (228587983828612233011552243, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_13, prime_ninetyThreeCM_37, prime_ninetyThreeCM_228587983828612233011552243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628884 : Nat.totient 109950820221562484078556628884 = 34563529692744582003844204800 := by
  rw [← show ((([(2, 2), (3, 5), (29, 1), (43, 1), (90712211547683563250201, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_29, prime_ninetyThreeCM_43, prime_ninetyThreeCM_90712211547683563250201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628885 : Nat.totient 109950820221562484078556628885 = 87933245564542835506141380864 := by
  rw [← show ((([(5, 1), (3209, 1), (6852653176787939175977353, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_5, prime_ninetyThreeCM_3209, prime_ninetyThreeCM_6852653176787939175977353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628886 : Nat.totient 109950820221562484078556628886 = 52585169917635091035821332800 := by
  rw [← show ((([(2, 1), (23, 1), (10578521, 1), (225951739587025453621, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_23, prime_ninetyThreeCM_10578521, prime_ninetyThreeCM_225951739587025453621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628887 : Nat.totient 109950820221562484078556628887 = 72784980683683743408728210592 := by
  rw [← show ((([(3, 1), (149, 1), (3083, 1), (79784297538106774524187, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_149, prime_ninetyThreeCM_3083, prime_ninetyThreeCM_79784297538106774524187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628888 : Nat.totient 109950820221562484078556628888 = 49977645444525489835619860480 := by
  rw [← show ((([(2, 3), (11, 1), (451346177, 1), (2768254618187209913, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_11, prime_ninetyThreeCM_451346177, prime_ninetyThreeCM_2768254618187209913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628889 : Nat.totient 109950820221562484078556628889 = 94243361587157699455068561456 := by
  rw [← show ((([(7, 1), (474533, 1), (33100458833530615236019, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_7, prime_ninetyThreeCM_474533, prime_ninetyThreeCM_33100458833530615236019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628890 : Nat.totient 109950820221562484078556628890 = 27777049253754497347470018048 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (19, 2), (424874449, 1), (23895130268707067, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_3, prime_ninetyThreeCM_5, prime_ninetyThreeCM_19, prime_ninetyThreeCM_424874449, prime_ninetyThreeCM_23895130268707067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628891 : Nat.totient 109950820221562484078556628891 = 109786675461570880068320139648 := by
  rw [← show ((([(677, 1), (63247, 1), (2567851320989378004689, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_677, prime_ninetyThreeCM_63247, prime_ninetyThreeCM_2567851320989378004689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628892 : Nat.totient 109950820221562484078556628892 = 54809321258482809283872639120 := by
  rw [← show ((([(2, 2), (331, 1), (83044426149216377702837333, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_331, prime_ninetyThreeCM_83044426149216377702837333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628893 : Nat.totient 109950820221562484078556628893 = 73088319525966950937363072000 := by
  rw [← show ((([(3, 2), (601, 1), (821, 1), (64709, 1), (382625267796556693, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_3, prime_ninetyThreeCM_601, prime_ninetyThreeCM_821, prime_ninetyThreeCM_64709, prime_ninetyThreeCM_382625267796556693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_ninetyThreeCM_109950820221562484078556628894 : Nat.totient 109950820221562484078556628894 = 54969535386011907645081477120 := by
  rw [← show ((([(2, 1), (18731, 1), (19037, 1), (1055809, 1), (146023799455889, 1)] : List FactorBlock).map factorBlockValue).prod) = 109950820221562484078556628894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_ninetyThreeCM_2, prime_ninetyThreeCM_18731, prime_ninetyThreeCM_19037, prime_ninetyThreeCM_1055809, prime_ninetyThreeCM_146023799455889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64NinetyThreeCM : certifiedKill 1 109950820221562484078556628792 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_ninetyThreeCM_109950820221562484078556628793, phi_ninetyThreeCM_109950820221562484078556628794, phi_ninetyThreeCM_109950820221562484078556628795,
    phi_ninetyThreeCM_109950820221562484078556628796, phi_ninetyThreeCM_109950820221562484078556628797, phi_ninetyThreeCM_109950820221562484078556628798,
    phi_ninetyThreeCM_109950820221562484078556628799, phi_ninetyThreeCM_109950820221562484078556628800, phi_ninetyThreeCM_109950820221562484078556628801,
    phi_ninetyThreeCM_109950820221562484078556628802, phi_ninetyThreeCM_109950820221562484078556628803, phi_ninetyThreeCM_109950820221562484078556628804,
    phi_ninetyThreeCM_109950820221562484078556628805, phi_ninetyThreeCM_109950820221562484078556628806, phi_ninetyThreeCM_109950820221562484078556628807,
    phi_ninetyThreeCM_109950820221562484078556628808, phi_ninetyThreeCM_109950820221562484078556628809, phi_ninetyThreeCM_109950820221562484078556628810,
    phi_ninetyThreeCM_109950820221562484078556628811, phi_ninetyThreeCM_109950820221562484078556628812, phi_ninetyThreeCM_109950820221562484078556628813,
    phi_ninetyThreeCM_109950820221562484078556628814, phi_ninetyThreeCM_109950820221562484078556628815, phi_ninetyThreeCM_109950820221562484078556628816,
    phi_ninetyThreeCM_109950820221562484078556628817, phi_ninetyThreeCM_109950820221562484078556628818, phi_ninetyThreeCM_109950820221562484078556628819,
    phi_ninetyThreeCM_109950820221562484078556628820, phi_ninetyThreeCM_109950820221562484078556628821, phi_ninetyThreeCM_109950820221562484078556628822,
    phi_ninetyThreeCM_109950820221562484078556628823, phi_ninetyThreeCM_109950820221562484078556628824, phi_ninetyThreeCM_109950820221562484078556628825,
    phi_ninetyThreeCM_109950820221562484078556628826, phi_ninetyThreeCM_109950820221562484078556628827, phi_ninetyThreeCM_109950820221562484078556628828,
    phi_ninetyThreeCM_109950820221562484078556628829, phi_ninetyThreeCM_109950820221562484078556628830, phi_ninetyThreeCM_109950820221562484078556628831,
    phi_ninetyThreeCM_109950820221562484078556628832, phi_ninetyThreeCM_109950820221562484078556628833, phi_ninetyThreeCM_109950820221562484078556628834,
    phi_ninetyThreeCM_109950820221562484078556628835, phi_ninetyThreeCM_109950820221562484078556628836, phi_ninetyThreeCM_109950820221562484078556628837,
    phi_ninetyThreeCM_109950820221562484078556628838, phi_ninetyThreeCM_109950820221562484078556628839, phi_ninetyThreeCM_109950820221562484078556628840,
    phi_ninetyThreeCM_109950820221562484078556628841, phi_ninetyThreeCM_109950820221562484078556628842, phi_ninetyThreeCM_109950820221562484078556628843,
    phi_ninetyThreeCM_109950820221562484078556628844, phi_ninetyThreeCM_109950820221562484078556628845, phi_ninetyThreeCM_109950820221562484078556628846,
    phi_ninetyThreeCM_109950820221562484078556628847, phi_ninetyThreeCM_109950820221562484078556628848, phi_ninetyThreeCM_109950820221562484078556628849,
    phi_ninetyThreeCM_109950820221562484078556628850, phi_ninetyThreeCM_109950820221562484078556628851, phi_ninetyThreeCM_109950820221562484078556628852,
    phi_ninetyThreeCM_109950820221562484078556628853, phi_ninetyThreeCM_109950820221562484078556628854, phi_ninetyThreeCM_109950820221562484078556628855,
    phi_ninetyThreeCM_109950820221562484078556628856, phi_ninetyThreeCM_109950820221562484078556628857, phi_ninetyThreeCM_109950820221562484078556628858,
    phi_ninetyThreeCM_109950820221562484078556628859, phi_ninetyThreeCM_109950820221562484078556628860, phi_ninetyThreeCM_109950820221562484078556628861,
    phi_ninetyThreeCM_109950820221562484078556628862, phi_ninetyThreeCM_109950820221562484078556628863, phi_ninetyThreeCM_109950820221562484078556628864,
    phi_ninetyThreeCM_109950820221562484078556628865, phi_ninetyThreeCM_109950820221562484078556628866, phi_ninetyThreeCM_109950820221562484078556628867,
    phi_ninetyThreeCM_109950820221562484078556628868, phi_ninetyThreeCM_109950820221562484078556628869, phi_ninetyThreeCM_109950820221562484078556628870,
    phi_ninetyThreeCM_109950820221562484078556628871, phi_ninetyThreeCM_109950820221562484078556628872, phi_ninetyThreeCM_109950820221562484078556628873,
    phi_ninetyThreeCM_109950820221562484078556628874, phi_ninetyThreeCM_109950820221562484078556628875, phi_ninetyThreeCM_109950820221562484078556628876,
    phi_ninetyThreeCM_109950820221562484078556628877, phi_ninetyThreeCM_109950820221562484078556628878, phi_ninetyThreeCM_109950820221562484078556628879,
    phi_ninetyThreeCM_109950820221562484078556628880, phi_ninetyThreeCM_109950820221562484078556628881, phi_ninetyThreeCM_109950820221562484078556628882,
    phi_ninetyThreeCM_109950820221562484078556628883, phi_ninetyThreeCM_109950820221562484078556628884, phi_ninetyThreeCM_109950820221562484078556628885,
    phi_ninetyThreeCM_109950820221562484078556628886, phi_ninetyThreeCM_109950820221562484078556628887, phi_ninetyThreeCM_109950820221562484078556628888,
    phi_ninetyThreeCM_109950820221562484078556628889, phi_ninetyThreeCM_109950820221562484078556628890, phi_ninetyThreeCM_109950820221562484078556628891,
    phi_ninetyThreeCM_109950820221562484078556628892, phi_ninetyThreeCM_109950820221562484078556628893, phi_ninetyThreeCM_109950820221562484078556628894
    ]

end TotientTailPeriodKiller
end Erdos249257
