import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredSixCZFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixCZFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixCZFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixCZFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixCZFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixCZFastPow a n * oneHundredSixCZFastPow a n * a else oneHundredSixCZFastPow a n * oneHundredSixCZFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixCZ_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredSixCZ_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredSixCZ_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredSixCZ_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredSixCZ_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredSixCZ_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredSixCZ_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredSixCZ_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredSixCZ_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredSixCZ_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredSixCZ_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredSixCZ_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredSixCZ_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredSixCZ_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredSixCZ_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredSixCZ_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredSixCZ_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredSixCZ_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredSixCZ_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredSixCZ_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredSixCZ_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredSixCZ_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredSixCZ_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredSixCZ_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredSixCZ_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredSixCZ_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredSixCZ_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredSixCZ_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredSixCZ_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredSixCZ_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredSixCZ_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredSixCZ_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredSixCZ_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredSixCZ_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredSixCZ_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredSixCZ_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredSixCZ_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredSixCZ_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredSixCZ_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredSixCZ_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredSixCZ_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredSixCZ_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredSixCZ_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredSixCZ_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredSixCZ_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredSixCZ_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredSixCZ_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredSixCZ_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredSixCZ_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredSixCZ_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredSixCZ_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredSixCZ_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredSixCZ_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredSixCZ_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredSixCZ_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredSixCZ_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredSixCZ_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredSixCZ_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredSixCZ_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredSixCZ_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredSixCZ_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredSixCZ_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredSixCZ_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredSixCZ_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredSixCZ_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredSixCZ_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredSixCZ_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredSixCZ_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredSixCZ_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredSixCZ_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredSixCZ_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredSixCZ_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredSixCZ_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredSixCZ_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredSixCZ_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredSixCZ_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredSixCZ_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredSixCZ_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredSixCZ_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredSixCZ_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredSixCZ_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredSixCZ_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredSixCZ_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredSixCZ_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredSixCZ_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredSixCZ_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredSixCZ_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredSixCZ_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredSixCZ_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredSixCZ_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredSixCZ_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredSixCZ_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredSixCZ_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredSixCZ_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredSixCZ_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredSixCZ_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredSixCZ_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredSixCZ_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredSixCZ_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredSixCZ_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredSixCZ_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredSixCZ_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredSixCZ_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredSixCZ_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredSixCZ_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredSixCZ_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredSixCZ_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredSixCZ_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredSixCZ_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredSixCZ_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredSixCZ_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredSixCZ_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredSixCZ_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_oneHundredSixCZ_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredSixCZ_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredSixCZ_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredSixCZ_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredSixCZ_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredSixCZ_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredSixCZ_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_oneHundredSixCZ_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredSixCZ_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_oneHundredSixCZ_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredSixCZ_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredSixCZ_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredSixCZ_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_oneHundredSixCZ_2179 : Nat.Prime 2179 := by norm_num

private theorem prime_oneHundredSixCZ_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_oneHundredSixCZ_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_oneHundredSixCZ_2341 : Nat.Prime 2341 := by norm_num

private theorem prime_oneHundredSixCZ_2417 : Nat.Prime 2417 := by norm_num

private theorem prime_oneHundredSixCZ_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_oneHundredSixCZ_2557 : Nat.Prime 2557 := by norm_num

private theorem prime_oneHundredSixCZ_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_oneHundredSixCZ_2687 : Nat.Prime 2687 := by norm_num

private theorem prime_oneHundredSixCZ_2749 : Nat.Prime 2749 := by norm_num

private theorem prime_oneHundredSixCZ_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_oneHundredSixCZ_2887 : Nat.Prime 2887 := by norm_num

private theorem prime_oneHundredSixCZ_2953 : Nat.Prime 2953 := by norm_num

private theorem prime_oneHundredSixCZ_3119 : Nat.Prime 3119 := by norm_num

private theorem prime_oneHundredSixCZ_3217 : Nat.Prime 3217 := by norm_num

private theorem prime_oneHundredSixCZ_3323 : Nat.Prime 3323 := by norm_num

private theorem prime_oneHundredSixCZ_3371 : Nat.Prime 3371 := by norm_num

private theorem prime_oneHundredSixCZ_3499 : Nat.Prime 3499 := by norm_num

private theorem prime_oneHundredSixCZ_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_oneHundredSixCZ_3613 : Nat.Prime 3613 := by norm_num

private theorem prime_oneHundredSixCZ_3719 : Nat.Prime 3719 := by norm_num

private theorem prime_oneHundredSixCZ_3803 : Nat.Prime 3803 := by norm_num

private theorem prime_oneHundredSixCZ_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredSixCZ_4007 : Nat.Prime 4007 := by norm_num

private theorem prime_oneHundredSixCZ_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_oneHundredSixCZ_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_oneHundredSixCZ_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_oneHundredSixCZ_4363 : Nat.Prime 4363 := by norm_num

private theorem prime_oneHundredSixCZ_4423 : Nat.Prime 4423 := by norm_num

private theorem prime_oneHundredSixCZ_4457 : Nat.Prime 4457 := by norm_num

private theorem prime_oneHundredSixCZ_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_oneHundredSixCZ_4751 : Nat.Prime 4751 := by norm_num

private theorem prime_oneHundredSixCZ_4909 : Nat.Prime 4909 := by norm_num

private theorem prime_oneHundredSixCZ_4919 : Nat.Prime 4919 := by norm_num

private theorem prime_oneHundredSixCZ_5233 : Nat.Prime 5233 := by norm_num

private theorem prime_oneHundredSixCZ_5479 : Nat.Prime 5479 := by norm_num

private theorem prime_oneHundredSixCZ_5527 : Nat.Prime 5527 := by norm_num

private theorem prime_oneHundredSixCZ_5701 : Nat.Prime 5701 := by norm_num

private theorem prime_oneHundredSixCZ_5743 : Nat.Prime 5743 := by norm_num

private theorem prime_oneHundredSixCZ_5851 : Nat.Prime 5851 := by norm_num

private theorem prime_oneHundredSixCZ_5861 : Nat.Prime 5861 := by norm_num

private theorem prime_oneHundredSixCZ_6311 : Nat.Prime 6311 := by norm_num

private theorem prime_oneHundredSixCZ_6337 : Nat.Prime 6337 := by norm_num

private theorem prime_oneHundredSixCZ_6373 : Nat.Prime 6373 := by norm_num

private theorem prime_oneHundredSixCZ_6473 : Nat.Prime 6473 := by norm_num

private theorem prime_oneHundredSixCZ_6899 : Nat.Prime 6899 := by norm_num

private theorem prime_oneHundredSixCZ_6917 : Nat.Prime 6917 := by norm_num

private theorem prime_oneHundredSixCZ_6977 : Nat.Prime 6977 := by norm_num

private theorem prime_oneHundredSixCZ_7043 : Nat.Prime 7043 := by norm_num

private theorem prime_oneHundredSixCZ_7321 : Nat.Prime 7321 := by norm_num

private theorem prime_oneHundredSixCZ_7417 : Nat.Prime 7417 := by norm_num

private theorem prime_oneHundredSixCZ_7537 : Nat.Prime 7537 := by norm_num

private theorem prime_oneHundredSixCZ_7603 : Nat.Prime 7603 := by norm_num

private theorem prime_oneHundredSixCZ_7823 : Nat.Prime 7823 := by norm_num

private theorem prime_oneHundredSixCZ_8009 : Nat.Prime 8009 := by norm_num

private theorem prime_oneHundredSixCZ_8053 : Nat.Prime 8053 := by norm_num

private theorem prime_oneHundredSixCZ_8171 : Nat.Prime 8171 := by norm_num

private theorem prime_oneHundredSixCZ_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredSixCZ_8647 : Nat.Prime 8647 := by norm_num

private theorem prime_oneHundredSixCZ_8803 : Nat.Prime 8803 := by norm_num

private theorem prime_oneHundredSixCZ_8837 : Nat.Prime 8837 := by norm_num

private theorem prime_oneHundredSixCZ_8999 : Nat.Prime 8999 := by norm_num

private theorem prime_oneHundredSixCZ_9133 : Nat.Prime 9133 := by norm_num

private theorem prime_oneHundredSixCZ_9199 : Nat.Prime 9199 := by norm_num

private theorem prime_oneHundredSixCZ_9281 : Nat.Prime 9281 := by norm_num

private theorem prime_oneHundredSixCZ_9403 : Nat.Prime 9403 := by norm_num

private theorem prime_oneHundredSixCZ_9473 : Nat.Prime 9473 := by norm_num

private theorem prime_oneHundredSixCZ_9689 : Nat.Prime 9689 := by norm_num

private theorem prime_oneHundredSixCZ_10111 : Nat.Prime 10111 := by norm_num

private theorem prime_oneHundredSixCZ_10433 : Nat.Prime 10433 := by norm_num

private theorem prime_oneHundredSixCZ_10949 : Nat.Prime 10949 := by norm_num

private theorem prime_oneHundredSixCZ_10973 : Nat.Prime 10973 := by norm_num

private theorem prime_oneHundredSixCZ_11251 : Nat.Prime 11251 := by norm_num

private theorem prime_oneHundredSixCZ_11443 : Nat.Prime 11443 := by norm_num

private theorem prime_oneHundredSixCZ_11657 : Nat.Prime 11657 := by norm_num

private theorem prime_oneHundredSixCZ_11717 : Nat.Prime 11717 := by norm_num

private theorem prime_oneHundredSixCZ_11731 : Nat.Prime 11731 := by norm_num

private theorem prime_oneHundredSixCZ_12109 : Nat.Prime 12109 := by norm_num

private theorem prime_oneHundredSixCZ_12211 : Nat.Prime 12211 := by norm_num

private theorem prime_oneHundredSixCZ_12227 : Nat.Prime 12227 := by norm_num

private theorem prime_oneHundredSixCZ_14011 : Nat.Prime 14011 := by norm_num

private theorem prime_oneHundredSixCZ_14207 : Nat.Prime 14207 := by norm_num

private theorem prime_oneHundredSixCZ_14593 : Nat.Prime 14593 := by norm_num

private theorem prime_oneHundredSixCZ_14797 : Nat.Prime 14797 := by norm_num

private theorem prime_oneHundredSixCZ_15383 : Nat.Prime 15383 := by norm_num

private theorem prime_oneHundredSixCZ_15473 : Nat.Prime 15473 := by norm_num

private theorem prime_oneHundredSixCZ_15667 : Nat.Prime 15667 := by norm_num

private theorem prime_oneHundredSixCZ_16843 : Nat.Prime 16843 := by norm_num

private theorem prime_oneHundredSixCZ_16943 : Nat.Prime 16943 := by norm_num

private theorem prime_oneHundredSixCZ_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredSixCZ_18251 : Nat.Prime 18251 := by norm_num

private theorem prime_oneHundredSixCZ_18743 : Nat.Prime 18743 := by norm_num

private theorem prime_oneHundredSixCZ_19301 : Nat.Prime 19301 := by norm_num

private theorem prime_oneHundredSixCZ_19687 : Nat.Prime 19687 := by norm_num

private theorem prime_oneHundredSixCZ_19889 : Nat.Prime 19889 := by norm_num

private theorem prime_oneHundredSixCZ_19963 : Nat.Prime 19963 := by norm_num

private theorem prime_oneHundredSixCZ_19997 : Nat.Prime 19997 := by norm_num

private theorem prime_oneHundredSixCZ_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredSixCZ_21487 : Nat.Prime 21487 := by norm_num

private theorem prime_oneHundredSixCZ_21767 : Nat.Prime 21767 := by norm_num

private theorem prime_oneHundredSixCZ_24733 : Nat.Prime 24733 := by norm_num

private theorem prime_oneHundredSixCZ_24923 : Nat.Prime 24923 := by norm_num

private theorem prime_oneHundredSixCZ_25127 : Nat.Prime 25127 := by norm_num

private theorem prime_oneHundredSixCZ_25763 : Nat.Prime 25763 := by norm_num

private theorem prime_oneHundredSixCZ_27541 : Nat.Prime 27541 := by norm_num

private theorem prime_oneHundredSixCZ_27751 : Nat.Prime 27751 := by norm_num

private theorem prime_oneHundredSixCZ_27763 : Nat.Prime 27763 := by norm_num

private theorem prime_oneHundredSixCZ_28001 : Nat.Prime 28001 := by norm_num

private theorem prime_oneHundredSixCZ_30137 : Nat.Prime 30137 := by norm_num

private theorem prime_oneHundredSixCZ_30253 : Nat.Prime 30253 := by norm_num

private theorem prime_oneHundredSixCZ_31321 : Nat.Prime 31321 := by norm_num

private theorem prime_oneHundredSixCZ_32299 : Nat.Prime 32299 := by norm_num

private theorem prime_oneHundredSixCZ_33851 : Nat.Prime 33851 := by norm_num

private theorem prime_oneHundredSixCZ_33941 : Nat.Prime 33941 := by norm_num

private theorem prime_oneHundredSixCZ_34589 : Nat.Prime 34589 := by norm_num

private theorem prime_oneHundredSixCZ_35831 : Nat.Prime 35831 := by norm_num

private theorem prime_oneHundredSixCZ_35963 : Nat.Prime 35963 := by norm_num

private theorem prime_oneHundredSixCZ_39521 : Nat.Prime 39521 := by norm_num

private theorem prime_oneHundredSixCZ_39607 : Nat.Prime 39607 := by norm_num

private theorem prime_oneHundredSixCZ_39883 : Nat.Prime 39883 := by norm_num

private theorem prime_oneHundredSixCZ_41117 : Nat.Prime 41117 := by norm_num

private theorem prime_oneHundredSixCZ_43481 : Nat.Prime 43481 := by norm_num

private theorem prime_oneHundredSixCZ_47221 : Nat.Prime 47221 := by norm_num

private theorem prime_oneHundredSixCZ_47527 : Nat.Prime 47527 := by norm_num

private theorem prime_oneHundredSixCZ_47533 : Nat.Prime 47533 := by norm_num

private theorem prime_oneHundredSixCZ_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredSixCZ_49853 : Nat.Prime 49853 := by norm_num

private theorem prime_oneHundredSixCZ_55103 : Nat.Prime 55103 := by norm_num

private theorem prime_oneHundredSixCZ_55117 : Nat.Prime 55117 := by norm_num

private theorem prime_oneHundredSixCZ_55243 : Nat.Prime 55243 := by norm_num

private theorem prime_oneHundredSixCZ_57731 : Nat.Prime 57731 := by norm_num

private theorem prime_oneHundredSixCZ_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredSixCZ_73243 : Nat.Prime 73243 := by norm_num

private theorem prime_oneHundredSixCZ_75011 : Nat.Prime 75011 := by norm_num

private theorem prime_oneHundredSixCZ_77731 : Nat.Prime 77731 := by norm_num

private theorem prime_oneHundredSixCZ_77983 : Nat.Prime 77983 := by norm_num

private theorem prime_oneHundredSixCZ_78311 : Nat.Prime 78311 := by norm_num

private theorem prime_oneHundredSixCZ_80233 : Nat.Prime 80233 := by norm_num

private theorem prime_oneHundredSixCZ_82237 : Nat.Prime 82237 := by norm_num

private theorem prime_oneHundredSixCZ_84067 : Nat.Prime 84067 := by norm_num

private theorem prime_oneHundredSixCZ_87583 : Nat.Prime 87583 := by norm_num

private theorem prime_oneHundredSixCZ_96329 : Nat.Prime 96329 := by norm_num

private theorem prime_oneHundredSixCZ_97159 : Nat.Prime 97159 := by norm_num

private theorem prime_oneHundredSixCZ_98731 : Nat.Prime 98731 := by norm_num

private theorem prime_oneHundredSixCZ_109859 : Nat.Prime 109859 := by norm_num

private theorem prime_oneHundredSixCZ_117679 : Nat.Prime 117679 := by norm_num

private theorem prime_oneHundredSixCZ_125929 : Nat.Prime 125929 := by norm_num

private theorem prime_oneHundredSixCZ_126047 : Nat.Prime 126047 := by norm_num

private theorem prime_oneHundredSixCZ_127277 : Nat.Prime 127277 := by norm_num

private theorem prime_oneHundredSixCZ_127363 : Nat.Prime 127363 := by norm_num

private theorem prime_oneHundredSixCZ_129959 : Nat.Prime 129959 := by norm_num

private theorem prime_oneHundredSixCZ_132283 : Nat.Prime 132283 := by norm_num

private theorem prime_oneHundredSixCZ_140407 : Nat.Prime 140407 := by norm_num

private theorem prime_oneHundredSixCZ_145517 : Nat.Prime 145517 := by norm_num

private theorem prime_oneHundredSixCZ_145543 : Nat.Prime 145543 := by norm_num

private theorem prime_oneHundredSixCZ_149491 : Nat.Prime 149491 := by norm_num

private theorem prime_oneHundredSixCZ_151243 : Nat.Prime 151243 := by norm_num

private theorem prime_oneHundredSixCZ_151381 : Nat.Prime 151381 := by norm_num

private theorem prime_oneHundredSixCZ_168143 : Nat.Prime 168143 := by norm_num

private theorem prime_oneHundredSixCZ_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredSixCZ_172751 : Nat.Prime 172751 := by norm_num

private theorem prime_oneHundredSixCZ_173273 : Nat.Prime 173273 := by norm_num

private theorem prime_oneHundredSixCZ_173659 : Nat.Prime 173659 := by norm_num

private theorem prime_oneHundredSixCZ_188983 : Nat.Prime 188983 := by norm_num

private theorem prime_oneHundredSixCZ_193247 : Nat.Prime 193247 := by norm_num

private theorem prime_oneHundredSixCZ_195281 : Nat.Prime 195281 := by norm_num

private theorem prime_oneHundredSixCZ_203897 : Nat.Prime 203897 := by norm_num

private theorem prime_oneHundredSixCZ_204173 : Nat.Prime 204173 := by norm_num

private theorem prime_oneHundredSixCZ_204443 : Nat.Prime 204443 := by norm_num

private theorem prime_oneHundredSixCZ_207877 : Nat.Prime 207877 := by norm_num

private theorem prime_oneHundredSixCZ_218143 : Nat.Prime 218143 := by norm_num

private theorem prime_oneHundredSixCZ_231551 : Nat.Prime 231551 := by norm_num

private theorem prime_oneHundredSixCZ_243809 : Nat.Prime 243809 := by norm_num

private theorem prime_oneHundredSixCZ_253801 : Nat.Prime 253801 := by norm_num

private theorem prime_oneHundredSixCZ_260329 : Nat.Prime 260329 := by norm_num

private theorem prime_oneHundredSixCZ_282767 : Nat.Prime 282767 := by norm_num

private theorem prime_oneHundredSixCZ_307423 : Nat.Prime 307423 := by norm_num

private theorem prime_oneHundredSixCZ_348911 : Nat.Prime 348911 := by norm_num

private theorem prime_oneHundredSixCZ_353963 : Nat.Prime 353963 := by norm_num

private theorem prime_oneHundredSixCZ_360511 : Nat.Prime 360511 := by norm_num

private theorem prime_oneHundredSixCZ_381223 : Nat.Prime 381223 := by norm_num

private theorem prime_oneHundredSixCZ_395453 : Nat.Prime 395453 := by norm_num

private theorem prime_oneHundredSixCZ_404191 : Nat.Prime 404191 := by norm_num

private theorem prime_oneHundredSixCZ_423389 : Nat.Prime 423389 := by norm_num

private theorem prime_oneHundredSixCZ_496999 : Nat.Prime 496999 := by norm_num

private theorem prime_oneHundredSixCZ_506699 : Nat.Prime 506699 := by norm_num

private theorem prime_oneHundredSixCZ_509653 : Nat.Prime 509653 := by norm_num

private theorem prime_oneHundredSixCZ_511963 : Nat.Prime 511963 := by norm_num

private theorem prime_oneHundredSixCZ_520837 : Nat.Prime 520837 := by norm_num

private theorem prime_oneHundredSixCZ_527347 : Nat.Prime 527347 := by norm_num

private theorem prime_oneHundredSixCZ_530063 : Nat.Prime 530063 := by norm_num

private theorem prime_oneHundredSixCZ_559841 : Nat.Prime 559841 := by norm_num

private theorem prime_oneHundredSixCZ_575087 : Nat.Prime 575087 := by norm_num

private theorem prime_oneHundredSixCZ_585367 : Nat.Prime 585367 := by norm_num

private theorem prime_oneHundredSixCZ_604907 : Nat.Prime 604907 := by norm_num

private theorem prime_oneHundredSixCZ_609397 : Nat.Prime 609397 := by norm_num

private theorem prime_oneHundredSixCZ_617531 : Nat.Prime 617531 := by norm_num

private theorem prime_oneHundredSixCZ_637873 : Nat.Prime 637873 := by norm_num

private theorem prime_oneHundredSixCZ_678499 : Nat.Prime 678499 := by norm_num

private theorem prime_oneHundredSixCZ_701507 : Nat.Prime 701507 := by norm_num

private theorem prime_oneHundredSixCZ_722971 : Nat.Prime 722971 := by norm_num

private theorem prime_oneHundredSixCZ_725111 : Nat.Prime 725111 := by norm_num

private theorem prime_oneHundredSixCZ_748933 : Nat.Prime 748933 := by norm_num

private theorem prime_oneHundredSixCZ_749659 : Nat.Prime 749659 := by norm_num

private theorem prime_oneHundredSixCZ_760187 : Nat.Prime 760187 := by norm_num

private theorem prime_oneHundredSixCZ_836951 : Nat.Prime 836951 := by norm_num

private theorem prime_oneHundredSixCZ_883973 : Nat.Prime 883973 := by norm_num

private theorem prime_oneHundredSixCZ_916259 : Nat.Prime 916259 := by norm_num

private theorem prime_oneHundredSixCZ_936917 : Nat.Prime 936917 := by norm_num

private theorem prime_oneHundredSixCZ_1004659 : Nat.Prime 1004659 := by norm_num

private theorem prime_oneHundredSixCZ_1017311 : Nat.Prime 1017311 := by norm_num

private theorem prime_oneHundredSixCZ_1095487 : Nat.Prime 1095487 := by norm_num

private theorem prime_oneHundredSixCZ_1135241 : Nat.Prime 1135241 := by norm_num

private theorem prime_oneHundredSixCZ_1163891 : Nat.Prime 1163891 := by norm_num

private theorem prime_oneHundredSixCZ_1177717 : Nat.Prime 1177717 := by norm_num

private theorem prime_oneHundredSixCZ_1245091 : Nat.Prime 1245091 := by norm_num

private theorem prime_oneHundredSixCZ_1259821 : Nat.Prime 1259821 := by norm_num

private theorem prime_oneHundredSixCZ_1260167 : Nat.Prime 1260167 := by norm_num

private theorem prime_oneHundredSixCZ_1292801 : Nat.Prime 1292801 := by norm_num

private theorem prime_oneHundredSixCZ_1369793 : Nat.Prime 1369793 := by norm_num

private theorem prime_oneHundredSixCZ_1430789 : Nat.Prime 1430789 := by norm_num

private theorem prime_oneHundredSixCZ_1493719 : Nat.Prime 1493719 := by norm_num

private theorem prime_oneHundredSixCZ_1510343 : Nat.Prime 1510343 := by norm_num

private theorem prime_oneHundredSixCZ_1712219 : Nat.Prime 1712219 := by norm_num

private theorem prime_oneHundredSixCZ_1723957 : Nat.Prime 1723957 := by norm_num

private theorem prime_oneHundredSixCZ_1754549 : Nat.Prime 1754549 := by norm_num

private theorem prime_oneHundredSixCZ_1807121 : Nat.Prime 1807121 := by norm_num

private theorem prime_oneHundredSixCZ_1818233 : Nat.Prime 1818233 := by norm_num

private theorem prime_oneHundredSixCZ_1861583 : Nat.Prime 1861583 := by norm_num

private theorem prime_oneHundredSixCZ_1863451 : Nat.Prime 1863451 := by norm_num

private theorem prime_oneHundredSixCZ_1893329 : Nat.Prime 1893329 := by norm_num

private theorem prime_oneHundredSixCZ_1911961 : Nat.Prime 1911961 := by norm_num

private theorem prime_oneHundredSixCZ_2045653 : Nat.Prime 2045653 := by norm_num

private theorem prime_oneHundredSixCZ_2156117 : Nat.Prime 2156117 := by norm_num

private theorem prime_oneHundredSixCZ_2235949 : Nat.Prime 2235949 := by norm_num

private theorem prime_oneHundredSixCZ_2287199 : Nat.Prime 2287199 := by norm_num

private theorem prime_oneHundredSixCZ_2323877 : Nat.Prime 2323877 := by norm_num

private theorem prime_oneHundredSixCZ_2388833 : Nat.Prime 2388833 := by norm_num

private theorem prime_oneHundredSixCZ_2576641 : Nat.Prime 2576641 := by norm_num

private theorem prime_oneHundredSixCZ_2904257 : Nat.Prime 2904257 := by norm_num

private theorem prime_oneHundredSixCZ_3051953 : Nat.Prime 3051953 := by norm_num

private theorem prime_oneHundredSixCZ_3080939 : Nat.Prime 3080939 := by norm_num

private theorem prime_oneHundredSixCZ_3110761 : Nat.Prime 3110761 := by norm_num

private theorem prime_oneHundredSixCZ_3128641 : Nat.Prime 3128641 := by norm_num

private theorem prime_oneHundredSixCZ_3150913 : Nat.Prime 3150913 := by norm_num

private theorem prime_oneHundredSixCZ_3980003 : Nat.Prime 3980003 := by norm_num

private theorem prime_oneHundredSixCZ_4065767 : Nat.Prime 4065767 := by norm_num

private theorem prime_oneHundredSixCZ_4255697 : Nat.Prime 4255697 := by norm_num

private theorem prime_oneHundredSixCZ_4357889 : Nat.Prime 4357889 := by norm_num

private theorem prime_oneHundredSixCZ_4502371 : Nat.Prime 4502371 := by norm_num

private theorem prime_oneHundredSixCZ_4731689 : Nat.Prime 4731689 := by norm_num

private theorem prime_oneHundredSixCZ_4762523 : Nat.Prime 4762523 := by norm_num

private theorem prime_oneHundredSixCZ_5213321 : Nat.Prime 5213321 := by norm_num

private theorem prime_oneHundredSixCZ_5328119 : Nat.Prime 5328119 := by norm_num

private theorem prime_oneHundredSixCZ_5669333 : Nat.Prime 5669333 := by norm_num

private theorem prime_oneHundredSixCZ_6140777 : Nat.Prime 6140777 := by norm_num

private theorem prime_oneHundredSixCZ_6870673 : Nat.Prime 6870673 := by norm_num

private theorem prime_oneHundredSixCZ_6930643 : Nat.Prime 6930643 := by norm_num

private theorem prime_oneHundredSixCZ_7281167 : Nat.Prime 7281167 := by norm_num

private theorem prime_oneHundredSixCZ_7461073 : Nat.Prime 7461073 := by norm_num

private theorem prime_oneHundredSixCZ_7633859 : Nat.Prime 7633859 := by norm_num

private theorem prime_oneHundredSixCZ_7808519 : Nat.Prime 7808519 := by norm_num

private theorem prime_oneHundredSixCZ_8552771 : Nat.Prime 8552771 := by norm_num

private theorem prime_oneHundredSixCZ_8630071 : Nat.Prime 8630071 := by norm_num

private theorem prime_oneHundredSixCZ_8761531 : Nat.Prime 8761531 := by norm_num

private theorem prime_oneHundredSixCZ_8826157 : Nat.Prime 8826157 := by norm_num

private theorem prime_oneHundredSixCZ_8951737 : Nat.Prime 8951737 := by norm_num

private theorem prime_oneHundredSixCZ_9860681 : Nat.Prime 9860681 := by norm_num

private theorem prime_oneHundredSixCZ_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredSixCZ_10934509 : Nat.Prime 10934509 := by norm_num

private theorem prime_oneHundredSixCZ_11088971 : Nat.Prime 11088971 := by norm_num

private theorem prime_oneHundredSixCZ_11292637 : Nat.Prime 11292637 := by norm_num

private theorem prime_oneHundredSixCZ_11913173 : Nat.Prime 11913173 := by norm_num

private theorem prime_oneHundredSixCZ_13224683 : Nat.Prime 13224683 := by norm_num

private theorem prime_oneHundredSixCZ_13435817 : Nat.Prime 13435817 := by norm_num

private theorem prime_oneHundredSixCZ_13970293 : Nat.Prime 13970293 := by norm_num

private theorem prime_oneHundredSixCZ_14986343 : Nat.Prime 14986343 := by norm_num

private theorem prime_oneHundredSixCZ_15287581 : Nat.Prime 15287581 := by norm_num

private theorem prime_oneHundredSixCZ_15581651 : Nat.Prime 15581651 := by norm_num

private theorem prime_oneHundredSixCZ_15626833 : Nat.Prime 15626833 := by norm_num

private theorem prime_oneHundredSixCZ_15834751 : Nat.Prime 15834751 := by norm_num

private theorem prime_oneHundredSixCZ_16185991 : Nat.Prime 16185991 := by norm_num

private theorem prime_oneHundredSixCZ_16235651 : Nat.Prime 16235651 := by norm_num

private theorem prime_oneHundredSixCZ_16240571 : Nat.Prime 16240571 := by norm_num

private theorem prime_oneHundredSixCZ_17409451 : Nat.Prime 17409451 := by norm_num

private theorem prime_oneHundredSixCZ_17725927 : Nat.Prime 17725927 := by norm_num

private theorem prime_oneHundredSixCZ_17757281 : Nat.Prime 17757281 := by norm_num

private theorem prime_oneHundredSixCZ_18058783 : Nat.Prime 18058783 := by norm_num

private theorem prime_oneHundredSixCZ_21048647 : Nat.Prime 21048647 := by norm_num

private theorem prime_oneHundredSixCZ_21355273 : Nat.Prime 21355273 := by norm_num

private theorem prime_oneHundredSixCZ_21438611 : Nat.Prime 21438611 := by norm_num

private theorem prime_oneHundredSixCZ_21696511 : Nat.Prime 21696511 := by norm_num

private theorem prime_oneHundredSixCZ_22175303 : Nat.Prime 22175303 := by norm_num

private theorem prime_oneHundredSixCZ_25669421 : Nat.Prime 25669421 := by norm_num

private theorem prime_oneHundredSixCZ_26755541 : Nat.Prime 26755541 := by norm_num

private theorem prime_oneHundredSixCZ_27249407 : Nat.Prime 27249407 := by norm_num

private theorem prime_oneHundredSixCZ_27630367 : Nat.Prime 27630367 := by norm_num

private theorem prime_oneHundredSixCZ_29648539 : Nat.Prime 29648539 := by norm_num

private theorem prime_oneHundredSixCZ_31107611 : Nat.Prime 31107611 := by
  apply lucas_primality 31107611 (2 : ZMod 31107611)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3110761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3110761, 1)] : List FactorBlock).map factorBlockValue).prod) = 31107611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_3110761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31107611) ^ 15553805 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31107611) ^ 6221522 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 31107611) ^ 10 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_32272609 : Nat.Prime 32272609 := by
  apply lucas_primality 32272609 (7 : ZMod 32272609)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (379, 1), (887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (379, 1), (887, 1)] : List FactorBlock).map factorBlockValue).prod) = 32272609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_379
      · exact prime_oneHundredSixCZ_887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 32272609) ^ 16136304 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 32272609) ^ 10757536 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 32272609) ^ 85152 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 32272609) ^ 36384 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_32408797 : Nat.Prime 32408797 := by
  apply lucas_primality 32408797 (2 : ZMod 32408797)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (55117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (55117, 1)] : List FactorBlock).map factorBlockValue).prod) = 32408797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_55117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32408797) ^ 16204398 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 32408797) ^ 10802932 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 32408797) ^ 4629828 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 32408797) ^ 588 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_33614963 : Nat.Prime 33614963 := by
  apply lucas_primality 33614963 (2 : ZMod 33614963)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (173273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (173273, 1)] : List FactorBlock).map factorBlockValue).prod) = 33614963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_97
      · exact prime_oneHundredSixCZ_173273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33614963) ^ 16807481 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 33614963) ^ 346546 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 33614963) ^ 194 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_39070043 : Nat.Prime 39070043 := by
  apply lucas_primality 39070043 (2 : ZMod 39070043)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (151, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (151, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) = 39070043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_151
      · exact prime_oneHundredSixCZ_619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39070043) ^ 19535021 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 39070043) ^ 3551822 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 39070043) ^ 2056318 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 39070043) ^ 258742 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 39070043) ^ 63118 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_42877223 : Nat.Prime 42877223 := by
  apply lucas_primality 42877223 (5 : ZMod 42877223)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21438611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21438611, 1)] : List FactorBlock).map factorBlockValue).prod) = 42877223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_21438611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 42877223) ^ 21438611 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 42877223) ^ 2 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_43687003 : Nat.Prime 43687003 := by
  apply lucas_primality 43687003 (3 : ZMod 43687003)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7281167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7281167, 1)] : List FactorBlock).map factorBlockValue).prod) = 43687003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7281167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 43687003) ^ 21843501 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 43687003) ^ 14562334 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 43687003) ^ 6 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_46253159 : Nat.Prime 46253159 := by
  apply lucas_primality 46253159 (7 : ZMod 46253159)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (17, 1), (27763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (17, 1), (27763, 1)] : List FactorBlock).map factorBlockValue).prod) = 46253159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_27763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 46253159) ^ 23126579 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 46253159) ^ 6607594 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 46253159) ^ 2720774 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 46253159) ^ 1666 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_46440283 : Nat.Prime 46440283 := by
  apply lucas_primality 46440283 (2 : ZMod 46440283)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (383, 1), (2887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (383, 1), (2887, 1)] : List FactorBlock).map factorBlockValue).prod) = 46440283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_383
      · exact prime_oneHundredSixCZ_2887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46440283) ^ 23220141 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 46440283) ^ 15480094 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 46440283) ^ 6634326 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 46440283) ^ 121254 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 46440283) ^ 16086 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_49983169 : Nat.Prime 49983169 := by
  apply lucas_primality 49983169 (13 : ZMod 49983169)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (260329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (260329, 1)] : List FactorBlock).map factorBlockValue).prod) = 49983169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_260329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 49983169) ^ 24991584 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 49983169) ^ 16661056 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 49983169) ^ 192 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_51316627 : Nat.Prime 51316627 := by
  apply lucas_primality 51316627 (2 : ZMod 51316627)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8552771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8552771, 1)] : List FactorBlock).map factorBlockValue).prod) = 51316627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_8552771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 51316627) ^ 25658313 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51316627) ^ 17105542 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51316627) ^ 6 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_58002107 : Nat.Prime 58002107 := by
  apply lucas_primality 58002107 (2 : ZMod 58002107)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (173659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (173659, 1)] : List FactorBlock).map factorBlockValue).prod) = 58002107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_167
      · exact prime_oneHundredSixCZ_173659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58002107) ^ 29001053 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 58002107) ^ 347318 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 58002107) ^ 334 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_1811
      · exact prime_oneHundredSixCZ_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_60225911 : Nat.Prime 60225911 := by
  apply lucas_primality 60225911 (7 : ZMod 60225911)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (98731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (98731, 1)] : List FactorBlock).map factorBlockValue).prod) = 60225911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_61
      · exact prime_oneHundredSixCZ_98731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 60225911) ^ 30112955 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 60225911) ^ 12045182 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 60225911) ^ 987310 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 60225911) ^ 610 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_61957069 : Nat.Prime 61957069 := by
  apply lucas_primality 61957069 (2 : ZMod 61957069)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (125929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (125929, 1)] : List FactorBlock).map factorBlockValue).prod) = 61957069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_125929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61957069) ^ 30978534 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 61957069) ^ 20652356 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 61957069) ^ 1511148 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 61957069) ^ 492 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_62542367 : Nat.Prime 62542367 := by
  apply lucas_primality 62542367 (5 : ZMod 62542367)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (401, 1), (77983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (401, 1), (77983, 1)] : List FactorBlock).map factorBlockValue).prod) = 62542367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_401
      · exact prime_oneHundredSixCZ_77983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 62542367) ^ 31271183 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 62542367) ^ 155966 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 62542367) ^ 802 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_64470877 : Nat.Prime 64470877 := by
  apply lucas_primality 64470877 (2 : ZMod 64470877)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (282767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (282767, 1)] : List FactorBlock).map factorBlockValue).prod) = 64470877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_282767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 64470877) ^ 32235438 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64470877) ^ 21490292 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64470877) ^ 3393204 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64470877) ^ 228 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_69702169 : Nat.Prime 69702169 := by
  apply lucas_primality 69702169 (17 : ZMod 69702169)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2904257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2904257, 1)] : List FactorBlock).map factorBlockValue).prod) = 69702169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_2904257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 69702169) ^ 34851084 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (17 : ZMod 69702169) ^ 23234056 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (17 : ZMod 69702169) ^ 24 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_71083819 : Nat.Prime 71083819 := by
  apply lucas_primality 71083819 (7 : ZMod 71083819)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (13, 1), (11251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (13, 1), (11251, 1)] : List FactorBlock).map factorBlockValue).prod) = 71083819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_11251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 71083819) ^ 35541909 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 71083819) ^ 23694606 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 71083819) ^ 5467986 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 71083819) ^ 6318 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_79913401 : Nat.Prime 79913401 := by
  apply lucas_primality 79913401 (11 : ZMod 79913401)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (7, 1), (53, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (7, 1), (53, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) = 79913401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_53
      · exact prime_oneHundredSixCZ_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 79913401) ^ 39956700 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 79913401) ^ 26637800 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 79913401) ^ 15982680 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 79913401) ^ 11416200 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 79913401) ^ 1507800 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 79913401) ^ 222600 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_82699231 : Nat.Prime 82699231 := by
  apply lucas_primality 82699231 (3 : ZMod 82699231)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (107, 1), (25763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (107, 1), (25763, 1)] : List FactorBlock).map factorBlockValue).prod) = 82699231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_107
      · exact prime_oneHundredSixCZ_25763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 82699231) ^ 41349615 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 82699231) ^ 27566410 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 82699231) ^ 16539846 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 82699231) ^ 772890 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 82699231) ^ 3210 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_85754447 : Nat.Prime 85754447 := by
  apply lucas_primality 85754447 (5 : ZMod 85754447)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42877223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42877223, 1)] : List FactorBlock).map factorBlockValue).prod) = 85754447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_42877223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 85754447) ^ 42877223 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 85754447) ^ 2 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_86666633 : Nat.Prime 86666633 := by
  apply lucas_primality 86666633 (3 : ZMod 86666633)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (191, 1), (4363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (191, 1), (4363, 1)] : List FactorBlock).map factorBlockValue).prod) = 86666633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_191
      · exact prime_oneHundredSixCZ_4363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 86666633) ^ 43333316 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 86666633) ^ 6666664 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 86666633) ^ 453752 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 86666633) ^ 19864 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_92207377 : Nat.Prime 92207377 := by
  apply lucas_primality 92207377 (10 : ZMod 92207377)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (461, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (461, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 92207377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_461
      · exact prime_oneHundredSixCZ_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 92207377) ^ 46103688 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 92207377) ^ 30735792 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 92207377) ^ 200016 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 92207377) ^ 199152 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_93770503 : Nat.Prime 93770503 := by
  apply lucas_primality 93770503 (3 : ZMod 93770503)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (317, 1), (7043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (317, 1), (7043, 1)] : List FactorBlock).map factorBlockValue).prod) = 93770503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_317
      · exact prime_oneHundredSixCZ_7043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93770503) ^ 46885251 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 93770503) ^ 31256834 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 93770503) ^ 13395786 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 93770503) ^ 295806 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 93770503) ^ 13314 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_95737399 : Nat.Prime 95737399 := by
  apply lucas_primality 95737399 (3 : ZMod 95737399)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (163, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (163, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) = 95737399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_53
      · exact prime_oneHundredSixCZ_163
      · exact prime_oneHundredSixCZ_1847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 95737399) ^ 47868699 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 95737399) ^ 31912466 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 95737399) ^ 1806366 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 95737399) ^ 587346 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 95737399) ^ 51834 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_106355563 : Nat.Prime 106355563 := by
  apply lucas_primality 106355563 (3 : ZMod 106355563)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17725927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17725927, 1)] : List FactorBlock).map factorBlockValue).prod) = 106355563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_17725927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 106355563) ^ 53177781 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 106355563) ^ 35451854 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 106355563) ^ 6 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_111765383 : Nat.Prime 111765383 := by
  apply lucas_primality 111765383 (7 : ZMod 111765383)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (1510343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (1510343, 1)] : List FactorBlock).map factorBlockValue).prod) = 111765383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_37
      · exact prime_oneHundredSixCZ_1510343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 111765383) ^ 55882691 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 111765383) ^ 3020686 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 111765383) ^ 74 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_116138233 : Nat.Prime 116138233 := by
  apply lucas_primality 116138233 (11 : ZMod 116138233)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 2), (10973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 2), (10973, 1)] : List FactorBlock).map factorBlockValue).prod) = 116138233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_10973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 116138233) ^ 58069116 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 116138233) ^ 38712744 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 116138233) ^ 16591176 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 116138233) ^ 10584 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_119270369 : Nat.Prime 119270369 := by
  apply lucas_primality 119270369 (3 : ZMod 119270369)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (17, 1), (31321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (17, 1), (31321, 1)] : List FactorBlock).map factorBlockValue).prod) = 119270369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_31321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 119270369) ^ 59635184 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 119270369) ^ 17038624 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 119270369) ^ 7015904 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 119270369) ^ 3808 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_125145641 : Nat.Prime 125145641 := by
  apply lucas_primality 125145641 (3 : ZMod 125145641)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (3128641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (3128641, 1)] : List FactorBlock).map factorBlockValue).prod) = 125145641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_3128641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 125145641) ^ 62572820 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 125145641) ^ 25029128 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 125145641) ^ 40 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_141334009 : Nat.Prime 141334009 := by
  apply lucas_primality 141334009 (14 : ZMod 141334009)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (281, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (281, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) = 141334009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_281
      · exact prime_oneHundredSixCZ_1103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 141334009) ^ 70667004 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (14 : ZMod 141334009) ^ 47111336 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (14 : ZMod 141334009) ^ 7438632 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (14 : ZMod 141334009) ^ 502968 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (14 : ZMod 141334009) ^ 128136 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_145774571 : Nat.Prime 145774571 := by
  apply lucas_primality 145774571 (6 : ZMod 145774571)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2557, 1), (5701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2557, 1), (5701, 1)] : List FactorBlock).map factorBlockValue).prod) = 145774571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_2557
      · exact prime_oneHundredSixCZ_5701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 145774571) ^ 72887285 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 145774571) ^ 29154914 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 145774571) ^ 57010 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 145774571) ^ 25570 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_166124341 : Nat.Prime 166124341 := by
  apply lucas_primality 166124341 (6 : ZMod 166124341)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (233, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (233, 2)] : List FactorBlock).map factorBlockValue).prod) = 166124341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 166124341) ^ 83062170 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 166124341) ^ 55374780 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 166124341) ^ 33224868 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 166124341) ^ 9772020 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 166124341) ^ 712980 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_168032911 : Nat.Prime 168032911 := by
  apply lucas_primality 168032911 (13 : ZMod 168032911)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (151381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (151381, 1)] : List FactorBlock).map factorBlockValue).prod) = 168032911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_37
      · exact prime_oneHundredSixCZ_151381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 168032911) ^ 84016455 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 168032911) ^ 56010970 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 168032911) ^ 33606582 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 168032911) ^ 4541430 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 168032911) ^ 1110 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_182125381 : Nat.Prime 182125381 := by
  apply lucas_primality 182125381 (10 : ZMod 182125381)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (479, 1), (6337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (479, 1), (6337, 1)] : List FactorBlock).map factorBlockValue).prod) = 182125381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_479
      · exact prime_oneHundredSixCZ_6337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 182125381) ^ 91062690 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 182125381) ^ 60708460 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 182125381) ^ 36425076 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 182125381) ^ 380220 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 182125381) ^ 28740 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_186168179 : Nat.Prime 186168179 := by
  apply lucas_primality 186168179 (2 : ZMod 186168179)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (113, 1), (117679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (113, 1), (117679, 1)] : List FactorBlock).map factorBlockValue).prod) = 186168179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_113
      · exact prime_oneHundredSixCZ_117679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 186168179) ^ 93084089 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 186168179) ^ 26595454 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 186168179) ^ 1647506 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 186168179) ^ 1582 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_194827813 : Nat.Prime 194827813 := by
  apply lucas_primality 194827813 (5 : ZMod 194827813)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (16235651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (16235651, 1)] : List FactorBlock).map factorBlockValue).prod) = 194827813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_16235651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 194827813) ^ 97413906 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 194827813) ^ 64942604 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 194827813) ^ 12 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_203692999 : Nat.Prime 203692999 := by
  apply lucas_primality 203692999 (3 : ZMod 203692999)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (506699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (506699, 1)] : List FactorBlock).map factorBlockValue).prod) = 203692999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_67
      · exact prime_oneHundredSixCZ_506699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 203692999) ^ 101846499 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 203692999) ^ 67897666 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 203692999) ^ 3040194 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 203692999) ^ 402 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_242715791 : Nat.Prime 242715791 := by
  apply lucas_primality 242715791 (13 : ZMod 242715791)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (836951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (836951, 1)] : List FactorBlock).map factorBlockValue).prod) = 242715791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_29
      · exact prime_oneHundredSixCZ_836951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 242715791) ^ 121357895 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 242715791) ^ 48543158 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 242715791) ^ 8369510 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 242715791) ^ 290 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_248970947 : Nat.Prime 248970947 := by
  apply lucas_primality 248970947 (5 : ZMod 248970947)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (43, 1), (21767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (43, 1), (21767, 1)] : List FactorBlock).map factorBlockValue).prod) = 248970947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_43
      · exact prime_oneHundredSixCZ_21767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 248970947) ^ 124485473 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 248970947) ^ 35567278 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 248970947) ^ 13103734 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 248970947) ^ 5790022 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 248970947) ^ 11438 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_264766231 : Nat.Prime 264766231 := by
  apply lucas_primality 264766231 (3 : ZMod 264766231)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (29, 1), (61, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (29, 1), (61, 1), (1663, 1)] : List FactorBlock).map factorBlockValue).prod) = 264766231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_29
      · exact prime_oneHundredSixCZ_61
      · exact prime_oneHundredSixCZ_1663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 264766231) ^ 132383115 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 264766231) ^ 88255410 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 264766231) ^ 52953246 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 264766231) ^ 9129870 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 264766231) ^ 4340430 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 264766231) ^ 159210 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_267741883 : Nat.Prime 267741883 := by
  apply lucas_primality 267741883 (2 : ZMod 267741883)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (59, 1), (4423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (59, 1), (4423, 1)] : List FactorBlock).map factorBlockValue).prod) = 267741883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_59
      · exact prime_oneHundredSixCZ_4423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 267741883) ^ 133870941 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 267741883) ^ 89247294 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 267741883) ^ 14091678 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 267741883) ^ 4537998 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 267741883) ^ 60534 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_284243513 : Nat.Prime 284243513 := by
  apply lucas_primality 284243513 (3 : ZMod 284243513)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (725111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (725111, 1)] : List FactorBlock).map factorBlockValue).prod) = 284243513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_725111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 284243513) ^ 142121756 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 284243513) ^ 40606216 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 284243513) ^ 392 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_291549143 : Nat.Prime 291549143 := by
  apply lucas_primality 291549143 (5 : ZMod 291549143)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (145774571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (145774571, 1)] : List FactorBlock).map factorBlockValue).prod) = 291549143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_145774571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 291549143) ^ 145774571 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 291549143) ^ 2 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_313060141 : Nat.Prime 313060141 := by
  apply lucas_primality 313060141 (10 : ZMod 313060141)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (193247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (193247, 1)] : List FactorBlock).map factorBlockValue).prod) = 313060141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_193247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 313060141) ^ 156530070 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 313060141) ^ 104353380 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 313060141) ^ 62612028 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 313060141) ^ 1620 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_325047851 : Nat.Prime 325047851 := by
  apply lucas_primality 325047851 (6 : ZMod 325047851)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2341, 1), (2777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2341, 1), (2777, 1)] : List FactorBlock).map factorBlockValue).prod) = 325047851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_2341
      · exact prime_oneHundredSixCZ_2777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 325047851) ^ 162523925 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 325047851) ^ 65009570 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 325047851) ^ 138850 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 325047851) ^ 117050 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_371773307 : Nat.Prime 371773307 := by
  apply lucas_primality 371773307 (2 : ZMod 371773307)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (10934509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (10934509, 1)] : List FactorBlock).map factorBlockValue).prod) = 371773307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_10934509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 371773307) ^ 185886653 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 371773307) ^ 21869018 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 371773307) ^ 34 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_381336383 : Nat.Prime 381336383 := by
  apply lucas_primality 381336383 (5 : ZMod 381336383)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (311, 1), (87583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (311, 1), (87583, 1)] : List FactorBlock).map factorBlockValue).prod) = 381336383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_311
      · exact prime_oneHundredSixCZ_87583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 381336383) ^ 190668191 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 381336383) ^ 54476626 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 381336383) ^ 1226162 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 381336383) ^ 4354 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_425422253 : Nat.Prime 425422253 := by
  apply lucas_primality 425422253 (2 : ZMod 425422253)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (106355563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (106355563, 1)] : List FactorBlock).map factorBlockValue).prod) = 425422253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_106355563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 425422253) ^ 212711126 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 425422253) ^ 4 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_485853773 : Nat.Prime 485853773 := by
  apply lucas_primality 485853773 (2 : ZMod 485853773)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (293, 1), (10111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (293, 1), (10111, 1)] : List FactorBlock).map factorBlockValue).prod) = 485853773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_293
      · exact prime_oneHundredSixCZ_10111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 485853773) ^ 242926886 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 485853773) ^ 11850092 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 485853773) ^ 1658204 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 485853773) ^ 48052 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_519698273 : Nat.Prime 519698273 := by
  apply lucas_primality 519698273 (3 : ZMod 519698273)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (16240571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (16240571, 1)] : List FactorBlock).map factorBlockValue).prod) = 519698273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_16240571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 519698273) ^ 259849136 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 519698273) ^ 32 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_525020833 : Nat.Prime 525020833 := by
  apply lucas_primality 525020833 (11 : ZMod 525020833)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (7, 1), (47, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (7, 1), (47, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) = 525020833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_47
      · exact prime_oneHundredSixCZ_1847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 525020833) ^ 262510416 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 525020833) ^ 175006944 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 525020833) ^ 75002976 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 525020833) ^ 11170656 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 525020833) ^ 284256 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_536152033 : Nat.Prime 536152033 := by
  apply lucas_primality 536152033 (11 : ZMod 536152033)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (13, 1), (19, 1), (7537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (13, 1), (19, 1), (7537, 1)] : List FactorBlock).map factorBlockValue).prod) = 536152033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_7537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 536152033) ^ 268076016 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 536152033) ^ 178717344 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 536152033) ^ 41242464 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 536152033) ^ 28218528 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 536152033) ^ 71136 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_546673783 : Nat.Prime 546673783 := by
  apply lucas_primality 546673783 (3 : ZMod 546673783)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (381223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (381223, 1)] : List FactorBlock).map factorBlockValue).prod) = 546673783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_239
      · exact prime_oneHundredSixCZ_381223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 546673783) ^ 273336891 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 546673783) ^ 182224594 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 546673783) ^ 2287338 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 546673783) ^ 1434 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_570404297 : Nat.Prime 570404297 := by
  apply lucas_primality 570404297 (5 : ZMod 570404297)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (11, 1), (132283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (11, 1), (132283, 1)] : List FactorBlock).map factorBlockValue).prod) = 570404297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_132283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 570404297) ^ 285202148 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 570404297) ^ 81486328 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 570404297) ^ 51854936 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 570404297) ^ 4312 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_598226891 : Nat.Prime 598226891 := by
  apply lucas_primality 598226891 (2 : ZMod 598226891)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (293, 1), (204173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (293, 1), (204173, 1)] : List FactorBlock).map factorBlockValue).prod) = 598226891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_293
      · exact prime_oneHundredSixCZ_204173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 598226891) ^ 299113445 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 598226891) ^ 119645378 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 598226891) ^ 2041730 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 598226891) ^ 2930 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_610806899 : Nat.Prime 610806899 := by
  apply lucas_primality 610806899 (6 : ZMod 610806899)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (1807121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (1807121, 1)] : List FactorBlock).map factorBlockValue).prod) = 610806899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_1807121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 610806899) ^ 305403449 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 610806899) ^ 46985146 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 610806899) ^ 338 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_643977463 : Nat.Prime 643977463 := by
  apply lucas_primality 643977463 (6 : ZMod 643977463)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3323, 1), (32299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3323, 1), (32299, 1)] : List FactorBlock).map factorBlockValue).prod) = 643977463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_3323
      · exact prime_oneHundredSixCZ_32299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 643977463) ^ 321988731 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 643977463) ^ 214659154 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 643977463) ^ 193794 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 643977463) ^ 19938 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_657598351 : Nat.Prime 657598351 := by
  apply lucas_primality 657598351 (6 : ZMod 657598351)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (31, 1), (103, 1), (1373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (31, 1), (103, 1), (1373, 1)] : List FactorBlock).map factorBlockValue).prod) = 657598351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_31
      · exact prime_oneHundredSixCZ_103
      · exact prime_oneHundredSixCZ_1373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 657598351) ^ 328799175 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 657598351) ^ 219199450 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 657598351) ^ 131519670 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 657598351) ^ 21212850 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 657598351) ^ 6384450 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 657598351) ^ 478950 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_17203
      · exact prime_oneHundredSixCZ_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_762426647 : Nat.Prime 762426647 := by
  apply lucas_primality 762426647 (5 : ZMod 762426647)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (137, 1), (229, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (137, 1), (229, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 762426647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_29
      · exact prime_oneHundredSixCZ_137
      · exact prime_oneHundredSixCZ_229
      · exact prime_oneHundredSixCZ_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 762426647) ^ 381213323 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 762426647) ^ 26290574 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 762426647) ^ 5565158 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 762426647) ^ 3329374 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 762426647) ^ 1819634 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_762672767 : Nat.Prime 762672767 := by
  apply lucas_primality 762672767 (5 : ZMod 762672767)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (381336383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (381336383, 1)] : List FactorBlock).map factorBlockValue).prod) = 762672767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_381336383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 762672767) ^ 381336383 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 762672767) ^ 2 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_783264863 : Nat.Prime 783264863 := by
  apply lucas_primality 783264863 (5 : ZMod 783264863)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (227, 1), (75011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (227, 1), (75011, 1)] : List FactorBlock).map factorBlockValue).prod) = 783264863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_23
      · exact prime_oneHundredSixCZ_227
      · exact prime_oneHundredSixCZ_75011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 783264863) ^ 391632431 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 783264863) ^ 34054994 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 783264863) ^ 3450506 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 783264863) ^ 10442 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_888401383 : Nat.Prime 888401383 := by
  apply lucas_primality 888401383 (5 : ZMod 888401383)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (89, 1), (151243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (89, 1), (151243, 1)] : List FactorBlock).map factorBlockValue).prod) = 888401383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_89
      · exact prime_oneHundredSixCZ_151243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 888401383) ^ 444200691 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 888401383) ^ 296133794 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 888401383) ^ 80763762 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 888401383) ^ 9982038 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 888401383) ^ 5874 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_937705031 : Nat.Prime 937705031 := by
  apply lucas_primality 937705031 (7 : ZMod 937705031)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (93770503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (93770503, 1)] : List FactorBlock).map factorBlockValue).prod) = 937705031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_93770503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 937705031) ^ 468852515 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 937705031) ^ 187541006 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 937705031) ^ 10 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_971707547 : Nat.Prime 971707547 := by
  apply lucas_primality 971707547 (2 : ZMod 971707547)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (485853773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (485853773, 1)] : List FactorBlock).map factorBlockValue).prod) = 971707547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_485853773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 971707547) ^ 485853773 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 971707547) ^ 2 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1008197467 : Nat.Prime 1008197467 := by
  apply lucas_primality 1008197467 (2 : ZMod 1008197467)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (168032911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (168032911, 1)] : List FactorBlock).map factorBlockValue).prod) = 1008197467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_168032911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1008197467) ^ 504098733 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008197467) ^ 336065822 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008197467) ^ 6 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1105425109 : Nat.Prime 1105425109 := by
  apply lucas_primality 1105425109 (10 : ZMod 1105425109)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (748933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (748933, 1)] : List FactorBlock).map factorBlockValue).prod) = 1105425109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_748933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1105425109) ^ 552712554 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 1105425109) ^ 368475036 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 1105425109) ^ 26961588 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 1105425109) ^ 1476 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1126682849 : Nat.Prime 1126682849 := by
  apply lucas_primality 1126682849 (3 : ZMod 1126682849)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (31, 1), (139, 1), (8171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (31, 1), (139, 1), (8171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1126682849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_31
      · exact prime_oneHundredSixCZ_139
      · exact prime_oneHundredSixCZ_8171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1126682849) ^ 563341424 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126682849) ^ 36344608 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126682849) ^ 8105632 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126682849) ^ 137888 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1426866403 : Nat.Prime 1426866403 := by
  apply lucas_primality 1426866403 (2 : ZMod 1426866403)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (607, 1), (30137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (607, 1), (30137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1426866403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_607
      · exact prime_oneHundredSixCZ_30137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1426866403) ^ 713433201 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1426866403) ^ 475622134 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1426866403) ^ 109758954 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1426866403) ^ 2350686 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1426866403) ^ 47346 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1438441219 : Nat.Prime 1438441219 := by
  apply lucas_primality 1438441219 (3 : ZMod 1438441219)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (79913401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (79913401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1438441219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_79913401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1438441219) ^ 719220609 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1438441219) ^ 479480406 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1438441219) ^ 18 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1725478681 : Nat.Prime 1725478681 := by
  apply lucas_primality 1725478681 (14 : ZMod 1725478681)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (97, 1), (271, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (97, 1), (271, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1725478681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_97
      · exact prime_oneHundredSixCZ_271
      · exact prime_oneHundredSixCZ_547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1725478681) ^ 862739340 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (14 : ZMod 1725478681) ^ 575159560 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (14 : ZMod 1725478681) ^ 345095736 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (14 : ZMod 1725478681) ^ 17788440 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (14 : ZMod 1725478681) ^ 6367080 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (14 : ZMod 1725478681) ^ 3154440 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1733332661 : Nat.Prime 1733332661 := by
  apply lucas_primality 1733332661 (3 : ZMod 1733332661)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (86666633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (86666633, 1)] : List FactorBlock).map factorBlockValue).prod) = 1733332661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_86666633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1733332661) ^ 866666330 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1733332661) ^ 346666532 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1733332661) ^ 20 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1815548851 : Nat.Prime 1815548851 := by
  apply lucas_primality 1815548851 (2 : ZMod 1815548851)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (167, 1), (8053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (167, 1), (8053, 1)] : List FactorBlock).map factorBlockValue).prod) = 1815548851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_167
      · exact prime_oneHundredSixCZ_8053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1815548851) ^ 907774425 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1815548851) ^ 605182950 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1815548851) ^ 363109770 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1815548851) ^ 10871550 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1815548851) ^ 225450 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1828808833 : Nat.Prime 1828808833 := by
  apply lucas_primality 1828808833 (5 : ZMod 1828808833)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (4762523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (4762523, 1)] : List FactorBlock).map factorBlockValue).prod) = 1828808833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_4762523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1828808833) ^ 914404416 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1828808833) ^ 609602944 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1828808833) ^ 384 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1948405247 : Nat.Prime 1948405247 := by
  apply lucas_primality 1948405247 (5 : ZMod 1948405247)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (151, 1), (77731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (151, 1), (77731, 1)] : List FactorBlock).map factorBlockValue).prod) = 1948405247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_83
      · exact prime_oneHundredSixCZ_151
      · exact prime_oneHundredSixCZ_77731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1948405247) ^ 974202623 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1948405247) ^ 23474762 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1948405247) ^ 12903346 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1948405247) ^ 25066 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2312752087 : Nat.Prime 2312752087 := by
  apply lucas_primality 2312752087 (3 : ZMod 2312752087)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (31, 1), (218143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (31, 1), (218143, 1)] : List FactorBlock).map factorBlockValue).prod) = 2312752087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_31
      · exact prime_oneHundredSixCZ_218143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2312752087) ^ 1156376043 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2312752087) ^ 770917362 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2312752087) ^ 121723794 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2312752087) ^ 74604906 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2312752087) ^ 10602 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2517718571 : Nat.Prime 2517718571 := by
  apply lucas_primality 2517718571 (7 : ZMod 2517718571)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (6140777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (6140777, 1)] : List FactorBlock).map factorBlockValue).prod) = 2517718571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_6140777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2517718571) ^ 1258859285 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2517718571) ^ 503543714 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2517718571) ^ 61407770 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2517718571) ^ 410 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2945622871 : Nat.Prime 2945622871 := by
  apply lucas_primality 2945622871 (3 : ZMod 2945622871)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (53, 1), (617531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (53, 1), (617531, 1)] : List FactorBlock).map factorBlockValue).prod) = 2945622871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_53
      · exact prime_oneHundredSixCZ_617531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2945622871) ^ 1472811435 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2945622871) ^ 981874290 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2945622871) ^ 589124574 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2945622871) ^ 55577790 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2945622871) ^ 4770 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_3623952329 : Nat.Prime 3623952329 := by
  apply lucas_primality 3623952329 (3 : ZMod 3623952329)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (1277, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (1277, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) = 3623952329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_31
      · exact prime_oneHundredSixCZ_1277
      · exact prime_oneHundredSixCZ_11443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3623952329) ^ 1811976164 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3623952329) ^ 116901688 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3623952329) ^ 2837864 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3623952329) ^ 316696 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_3691530701 : Nat.Prime 3691530701 := by
  apply lucas_primality 3691530701 (2 : ZMod 3691530701)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (13, 1), (37, 1), (6977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (13, 1), (37, 1), (6977, 1)] : List FactorBlock).map factorBlockValue).prod) = 3691530701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_37
      · exact prime_oneHundredSixCZ_6977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3691530701) ^ 1845765350 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3691530701) ^ 738306140 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3691530701) ^ 335593700 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3691530701) ^ 283963900 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3691530701) ^ 99771100 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3691530701) ^ 529100 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_3809923631 : Nat.Prime 3809923631 := by
  apply lucas_primality 3809923631 (13 : ZMod 3809923631)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (431, 1), (883973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (431, 1), (883973, 1)] : List FactorBlock).map factorBlockValue).prod) = 3809923631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_431
      · exact prime_oneHundredSixCZ_883973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3809923631) ^ 1904961815 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3809923631) ^ 761984726 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3809923631) ^ 8839730 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3809923631) ^ 4310 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_4240020271 : Nat.Prime 4240020271 := by
  apply lucas_primality 4240020271 (3 : ZMod 4240020271)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (141334009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (141334009, 1)] : List FactorBlock).map factorBlockValue).prod) = 4240020271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_141334009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4240020271) ^ 2120010135 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4240020271) ^ 1413340090 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4240020271) ^ 848004054 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4240020271) ^ 30 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_4683745333 : Nat.Prime 4683745333 := by
  apply lucas_primality 4683745333 (2 : ZMod 4683745333)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (47, 1), (395453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (47, 1), (395453, 1)] : List FactorBlock).map factorBlockValue).prod) = 4683745333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_47
      · exact prime_oneHundredSixCZ_395453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4683745333) ^ 2341872666 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4683745333) ^ 1561248444 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4683745333) ^ 669106476 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4683745333) ^ 99654156 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4683745333) ^ 11844 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_5383815341 : Nat.Prime 5383815341 := by
  apply lucas_primality 5383815341 (2 : ZMod 5383815341)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (15834751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (15834751, 1)] : List FactorBlock).map factorBlockValue).prod) = 5383815341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_15834751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5383815341) ^ 2691907670 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5383815341) ^ 1076763068 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5383815341) ^ 316695020 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5383815341) ^ 340 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_5628813031 : Nat.Prime 5628813031 := by
  apply lucas_primality 5628813031 (6 : ZMod 5628813031)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (62542367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (62542367, 1)] : List FactorBlock).map factorBlockValue).prod) = 5628813031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_62542367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5628813031) ^ 2814406515 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 5628813031) ^ 1876271010 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 5628813031) ^ 1125762606 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 5628813031) ^ 90 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_31
      · exact prime_oneHundredSixCZ_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_6322483171 : Nat.Prime 6322483171 := by
  apply lucas_primality 6322483171 (2 : ZMod 6322483171)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (31, 1), (241, 1), (9403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (31, 1), (241, 1), (9403, 1)] : List FactorBlock).map factorBlockValue).prod) = 6322483171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_31
      · exact prime_oneHundredSixCZ_241
      · exact prime_oneHundredSixCZ_9403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6322483171) ^ 3161241585 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6322483171) ^ 2107494390 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6322483171) ^ 1264496634 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6322483171) ^ 203951070 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6322483171) ^ 26234370 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6322483171) ^ 672390 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_6504558913 : Nat.Prime 6504558913 := by
  apply lucas_primality 6504558913 (7 : ZMod 6504558913)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (11292637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (11292637, 1)] : List FactorBlock).map factorBlockValue).prod) = 6504558913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_11292637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 6504558913) ^ 3252279456 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 6504558913) ^ 2168186304 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 6504558913) ^ 576 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_7383061403 : Nat.Prime 7383061403 := by
  apply lucas_primality 7383061403 (2 : ZMod 7383061403)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3691530701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3691530701, 1)] : List FactorBlock).map factorBlockValue).prod) = 7383061403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3691530701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7383061403) ^ 3691530701 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7383061403) ^ 2 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_7677987853 : Nat.Prime 7677987853 := by
  apply lucas_primality 7677987853 (11 : ZMod 7677987853)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2521, 1), (253801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2521, 1), (253801, 1)] : List FactorBlock).map factorBlockValue).prod) = 7677987853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_2521
      · exact prime_oneHundredSixCZ_253801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7677987853) ^ 3838993926 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 7677987853) ^ 2559329284 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 7677987853) ^ 3045612 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 7677987853) ^ 30252 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_7995888361 : Nat.Prime 7995888361 := by
  apply lucas_primality 7995888361 (11 : ZMod 7995888361)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (23, 1), (241, 1), (4007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (23, 1), (241, 1), (4007, 1)] : List FactorBlock).map factorBlockValue).prod) = 7995888361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_23
      · exact prime_oneHundredSixCZ_241
      · exact prime_oneHundredSixCZ_4007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7995888361) ^ 3997944180 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 7995888361) ^ 2665296120 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 7995888361) ^ 1599177672 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 7995888361) ^ 347647320 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 7995888361) ^ 33177960 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 7995888361) ^ 1995480 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_8134821047 : Nat.Prime 8134821047 := by
  apply lucas_primality 8134821047 (5 : ZMod 8134821047)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (33614963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (33614963, 1)] : List FactorBlock).map factorBlockValue).prod) = 8134821047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_33614963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8134821047) ^ 4067410523 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 8134821047) ^ 739529186 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 8134821047) ^ 242 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_8293563323 : Nat.Prime 8293563323 := by
  apply lucas_primality 8293563323 (2 : ZMod 8293563323)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (22175303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (22175303, 1)] : List FactorBlock).map factorBlockValue).prod) = 8293563323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_22175303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8293563323) ^ 4146781661 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8293563323) ^ 753960302 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8293563323) ^ 487856666 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8293563323) ^ 374 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_8900480053 : Nat.Prime 8900480053 := by
  apply lucas_primality 8900480053 (2 : ZMod 8900480053)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (47, 1), (191, 1), (27541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (47, 1), (191, 1), (27541, 1)] : List FactorBlock).map factorBlockValue).prod) = 8900480053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_47
      · exact prime_oneHundredSixCZ_191
      · exact prime_oneHundredSixCZ_27541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8900480053) ^ 4450240026 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8900480053) ^ 2966826684 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8900480053) ^ 189371916 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8900480053) ^ 46599372 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8900480053) ^ 323172 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_9239445521 : Nat.Prime 9239445521 := by
  apply lucas_primality 9239445521 (3 : ZMod 9239445521)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (61, 1), (1893329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (61, 1), (1893329, 1)] : List FactorBlock).map factorBlockValue).prod) = 9239445521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_61
      · exact prime_oneHundredSixCZ_1893329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9239445521) ^ 4619722760 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9239445521) ^ 1847889104 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9239445521) ^ 151466320 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9239445521) ^ 4880 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_9635211779 : Nat.Prime 9635211779 := by
  apply lucas_primality 9635211779 (2 : ZMod 9635211779)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (166124341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (166124341, 1)] : List FactorBlock).map factorBlockValue).prod) = 9635211779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_29
      · exact prime_oneHundredSixCZ_166124341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9635211779) ^ 4817605889 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9635211779) ^ 332248682 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9635211779) ^ 58 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_10408787593 : Nat.Prime 10408787593 := by
  apply lucas_primality 10408787593 (5 : ZMod 10408787593)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (61957069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (61957069, 1)] : List FactorBlock).map factorBlockValue).prod) = 10408787593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_61957069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10408787593) ^ 5204393796 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 10408787593) ^ 3469595864 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 10408787593) ^ 1486969656 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 10408787593) ^ 168 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_10767630683 : Nat.Prime 10767630683 := by
  apply lucas_primality 10767630683 (2 : ZMod 10767630683)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5383815341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5383815341, 1)] : List FactorBlock).map factorBlockValue).prod) = 10767630683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5383815341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 10767630683) ^ 5383815341 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 10767630683) ^ 2 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_10938675403 : Nat.Prime 10938675403 := by
  apply lucas_primality 10938675403 (2 : ZMod 10938675403)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (59, 1), (137, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (59, 1), (137, 1), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 10938675403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_59
      · exact prime_oneHundredSixCZ_137
      · exact prime_oneHundredSixCZ_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10938675403) ^ 5469337701 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 10938675403) ^ 3646225134 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 10938675403) ^ 575719758 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 10938675403) ^ 185401278 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 10938675403) ^ 79844346 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 10938675403) ^ 8293158 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_14414699807 : Nat.Prime 14414699807 := by
  apply lucas_primality 14414699807 (5 : ZMod 14414699807)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 2), (29, 1), (83, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 2), (29, 1), (83, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) = 14414699807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_29
      · exact prime_oneHundredSixCZ_83
      · exact prime_oneHundredSixCZ_797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14414699807) ^ 7207349903 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 14414699807) ^ 1108823062 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 14414699807) ^ 847923518 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 14414699807) ^ 497058614 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 14414699807) ^ 173671082 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 14414699807) ^ 18086198 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_14689556407 : Nat.Prime 14689556407 := by
  apply lucas_primality 14689556407 (3 : ZMod 14689556407)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (37, 1), (3150913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (37, 1), (3150913, 1)] : List FactorBlock).map factorBlockValue).prod) = 14689556407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_37
      · exact prime_oneHundredSixCZ_3150913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14689556407) ^ 7344778203 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 14689556407) ^ 4896518802 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 14689556407) ^ 2098508058 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 14689556407) ^ 397015038 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 14689556407) ^ 4662 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_16092631393 : Nat.Prime 16092631393 := by
  apply lucas_primality 16092631393 (5 : ZMod 16092631393)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (9860681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (9860681, 1)] : List FactorBlock).map factorBlockValue).prod) = 16092631393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_9860681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16092631393) ^ 8046315696 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 16092631393) ^ 5364210464 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 16092631393) ^ 946625376 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 16092631393) ^ 1632 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_16504544513 : Nat.Prime 16504544513 := by
  apply lucas_primality 16504544513 (3 : ZMod 16504544513)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (64470877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (64470877, 1)] : List FactorBlock).map factorBlockValue).prod) = 16504544513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_64470877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 16504544513) ^ 8252272256 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 16504544513) ^ 256 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_18887317177 : Nat.Prime 18887317177 := by
  apply lucas_primality 18887317177 (15 : ZMod 18887317177)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (31, 2), (8999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (31, 2), (8999, 1)] : List FactorBlock).map factorBlockValue).prod) = 18887317177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_31
      · exact prime_oneHundredSixCZ_8999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 18887317177) ^ 9443658588 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (15 : ZMod 18887317177) ^ 6295772392 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (15 : ZMod 18887317177) ^ 2698188168 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (15 : ZMod 18887317177) ^ 1452870552 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (15 : ZMod 18887317177) ^ 609268296 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (15 : ZMod 18887317177) ^ 2098824 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_21860883103 : Nat.Prime 21860883103 := by
  apply lucas_primality 21860883103 (3 : ZMod 21860883103)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (51316627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (51316627, 1)] : List FactorBlock).map factorBlockValue).prod) = 21860883103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_71
      · exact prime_oneHundredSixCZ_51316627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 21860883103) ^ 10930441551 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 21860883103) ^ 7286961034 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 21860883103) ^ 307899762 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 21860883103) ^ 426 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_25207362881 : Nat.Prime 25207362881 := by
  apply lucas_primality 25207362881 (3 : ZMod 25207362881)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (71, 1), (353, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (71, 1), (353, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 25207362881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_71
      · exact prime_oneHundredSixCZ_353
      · exact prime_oneHundredSixCZ_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25207362881) ^ 12603681440 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 25207362881) ^ 5041472576 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 25207362881) ^ 3601051840 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 25207362881) ^ 355033280 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 25207362881) ^ 71408960 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 25207362881) ^ 56141120 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_27197869187 : Nat.Prime 27197869187 := by
  apply lucas_primality 27197869187 (2 : ZMod 27197869187)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (193, 1), (243809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (193, 1), (243809, 1)] : List FactorBlock).map factorBlockValue).prod) = 27197869187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_193
      · exact prime_oneHundredSixCZ_243809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27197869187) ^ 13598934593 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 27197869187) ^ 1599874658 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 27197869187) ^ 140921602 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 27197869187) ^ 111554 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_28422218221 : Nat.Prime 28422218221 := by
  apply lucas_primality 28422218221 (10 : ZMod 28422218221)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (37, 1), (1163891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (37, 1), (1163891, 1)] : List FactorBlock).map factorBlockValue).prod) = 28422218221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_37
      · exact prime_oneHundredSixCZ_1163891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 28422218221) ^ 14211109110 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 28422218221) ^ 9474072740 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 28422218221) ^ 5684443644 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 28422218221) ^ 2583838020 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 28422218221) ^ 768168060 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 28422218221) ^ 24420 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_28551438473 : Nat.Prime 28551438473 := by
  apply lucas_primality 28551438473 (5 : ZMod 28551438473)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (131, 1), (157, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (131, 1), (157, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) = 28551438473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_131
      · exact prime_oneHundredSixCZ_157
      · exact prime_oneHundredSixCZ_9133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 28551438473) ^ 14275719236 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 28551438473) ^ 1502707288 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 28551438473) ^ 217949912 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 28551438473) ^ 181856296 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 28551438473) ^ 3126184 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_32822565421 : Nat.Prime 32822565421 := by
  apply lucas_primality 32822565421 (6 : ZMod 32822565421)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (229, 1), (2388833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (229, 1), (2388833, 1)] : List FactorBlock).map factorBlockValue).prod) = 32822565421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_229
      · exact prime_oneHundredSixCZ_2388833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 32822565421) ^ 16411282710 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 32822565421) ^ 10940855140 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 32822565421) ^ 6564513084 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 32822565421) ^ 143329980 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 32822565421) ^ 13740 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_33769121923 : Nat.Prime 33769121923 := by
  apply lucas_primality 33769121923 (3 : ZMod 33769121923)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109, 1), (3499, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109, 1), (3499, 1), (4919, 1)] : List FactorBlock).map factorBlockValue).prod) = 33769121923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_109
      · exact prime_oneHundredSixCZ_3499
      · exact prime_oneHundredSixCZ_4919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33769121923) ^ 16884560961 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 33769121923) ^ 11256373974 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 33769121923) ^ 309808458 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 33769121923) ^ 9651078 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 33769121923) ^ 6865038 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_34543175743 : Nat.Prime 34543175743 := by
  apply lucas_primality 34543175743 (3 : ZMod 34543175743)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (71, 1), (575087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (71, 1), (575087, 1)] : List FactorBlock).map factorBlockValue).prod) = 34543175743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_47
      · exact prime_oneHundredSixCZ_71
      · exact prime_oneHundredSixCZ_575087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34543175743) ^ 17271587871 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 34543175743) ^ 11514391914 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 34543175743) ^ 734961186 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 34543175743) ^ 486523602 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 34543175743) ^ 60066 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_34631756843 : Nat.Prime 34631756843 := by
  apply lucas_primality 34631756843 (2 : ZMod 34631756843)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (557, 1), (722971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (557, 1), (722971, 1)] : List FactorBlock).map factorBlockValue).prod) = 34631756843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_43
      · exact prime_oneHundredSixCZ_557
      · exact prime_oneHundredSixCZ_722971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34631756843) ^ 17315878421 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 34631756843) ^ 805389694 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 34631756843) ^ 62175506 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 34631756843) ^ 47902 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_34985897161 : Nat.Prime 34985897161 := by
  apply lucas_primality 34985897161 (7 : ZMod 34985897161)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (291549143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (291549143, 1)] : List FactorBlock).map factorBlockValue).prod) = 34985897161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_291549143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 34985897161) ^ 17492948580 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 34985897161) ^ 11661965720 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 34985897161) ^ 6997179432 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 34985897161) ^ 120 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_35601920213 : Nat.Prime 35601920213 := by
  apply lucas_primality 35601920213 (2 : ZMod 35601920213)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8900480053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8900480053, 1)] : List FactorBlock).map factorBlockValue).prod) = 35601920213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_8900480053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 35601920213) ^ 17800960106 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 35601920213) ^ 4 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_51635320351 : Nat.Prime 51635320351 := by
  apply lucas_primality 51635320351 (3 : ZMod 51635320351)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (79, 1), (557, 1), (7823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (79, 1), (557, 1), (7823, 1)] : List FactorBlock).map factorBlockValue).prod) = 51635320351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_79
      · exact prime_oneHundredSixCZ_557
      · exact prime_oneHundredSixCZ_7823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51635320351) ^ 25817660175 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 51635320351) ^ 17211773450 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 51635320351) ^ 10327064070 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 51635320351) ^ 653611650 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 51635320351) ^ 92702550 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 51635320351) ^ 6600450 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_54667378301 : Nat.Prime 54667378301 := by
  apply lucas_primality 54667378301 (2 : ZMod 54667378301)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (546673783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (546673783, 1)] : List FactorBlock).map factorBlockValue).prod) = 54667378301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_546673783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 54667378301) ^ 27333689150 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 54667378301) ^ 10933475660 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 54667378301) ^ 100 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_64171299547 : Nat.Prime 64171299547 := by
  apply lucas_primality 64171299547 (2 : ZMod 64171299547)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (23, 1), (637873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (23, 1), (637873, 1)] : List FactorBlock).map factorBlockValue).prod) = 64171299547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_23
      · exact prime_oneHundredSixCZ_637873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 64171299547) ^ 32085649773 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64171299547) ^ 21390433182 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64171299547) ^ 2790056502 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64171299547) ^ 100602 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_64825442039 : Nat.Prime 64825442039 := by
  apply lucas_primality 64825442039 (7 : ZMod 64825442039)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (125145641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (125145641, 1)] : List FactorBlock).map factorBlockValue).prod) = 64825442039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_37
      · exact prime_oneHundredSixCZ_125145641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 64825442039) ^ 32412721019 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 64825442039) ^ 9260777434 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 64825442039) ^ 1752038974 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 64825442039) ^ 518 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_77914288607 : Nat.Prime 77914288607 := by
  apply lucas_primality 77914288607 (5 : ZMod 77914288607)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (73, 1), (6930643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (73, 1), (6930643, 1)] : List FactorBlock).map factorBlockValue).prod) = 77914288607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_73
      · exact prime_oneHundredSixCZ_6930643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 77914288607) ^ 38957144303 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 77914288607) ^ 11130612658 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 77914288607) ^ 7083117146 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 77914288607) ^ 1067319022 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 77914288607) ^ 11242 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_82857392227 : Nat.Prime 82857392227 := by
  apply lucas_primality 82857392227 (3 : ZMod 82857392227)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (657598351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (657598351, 1)] : List FactorBlock).map factorBlockValue).prod) = 82857392227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_657598351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 82857392227) ^ 41428696113 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 82857392227) ^ 27619130742 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 82857392227) ^ 11836770318 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 82857392227) ^ 126 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_90127888943 : Nat.Prime 90127888943 := by
  apply lucas_primality 90127888943 (10 : ZMod 90127888943)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 2), (17, 1), (59, 1), (163, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 2), (17, 1), (59, 1), (163, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) = 90127888943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_59
      · exact prime_oneHundredSixCZ_163
      · exact prime_oneHundredSixCZ_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 90127888943) ^ 45063944471 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 90127888943) ^ 12875412706 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 90127888943) ^ 6932914534 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 90127888943) ^ 5301640526 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 90127888943) ^ 1527591338 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 90127888943) ^ 552931834 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 90127888943) ^ 386814974 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_96753101927 : Nat.Prime 96753101927 := by
  apply lucas_primality 96753101927 (5 : ZMod 96753101927)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2953, 1), (1260167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2953, 1), (1260167, 1)] : List FactorBlock).map factorBlockValue).prod) = 96753101927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_2953
      · exact prime_oneHundredSixCZ_1260167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 96753101927) ^ 48376550963 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 96753101927) ^ 7442546302 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 96753101927) ^ 32764342 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 96753101927) ^ 76778 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_115092690637 : Nat.Prime 115092690637 := by
  apply lucas_primality 115092690637 (2 : ZMod 115092690637)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (41, 1), (739, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (41, 1), (739, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) = 115092690637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_739
      · exact prime_oneHundredSixCZ_4111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 115092690637) ^ 57546345318 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 115092690637) ^ 38364230212 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 115092690637) ^ 16441812948 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 115092690637) ^ 10462971876 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 115092690637) ^ 2807138796 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 115092690637) ^ 155741124 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 115092690637) ^ 27996276 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_115436188111 : Nat.Prime 115436188111 := by
  apply lucas_primality 115436188111 (6 : ZMod 115436188111)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (347, 1), (11088971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (347, 1), (11088971, 1)] : List FactorBlock).map factorBlockValue).prod) = 115436188111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_347
      · exact prime_oneHundredSixCZ_11088971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 115436188111) ^ 57718094055 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 115436188111) ^ 38478729370 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 115436188111) ^ 23087237622 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 115436188111) ^ 332669130 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 115436188111) ^ 10410 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_122635811411 : Nat.Prime 122635811411 := by
  apply lucas_primality 122635811411 (6 : ZMod 122635811411)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (19, 1), (92207377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (19, 1), (92207377, 1)] : List FactorBlock).map factorBlockValue).prod) = 122635811411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_92207377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 122635811411) ^ 61317905705 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 122635811411) ^ 24527162282 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 122635811411) ^ 17519401630 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 122635811411) ^ 6454516390 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 122635811411) ^ 1330 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_184411739483 : Nat.Prime 184411739483 := by
  apply lucas_primality 184411739483 (2 : ZMod 184411739483)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1531, 1), (60225911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1531, 1), (60225911, 1)] : List FactorBlock).map factorBlockValue).prod) = 184411739483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_1531
      · exact prime_oneHundredSixCZ_60225911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 184411739483) ^ 92205869741 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 184411739483) ^ 120451822 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 184411739483) ^ 3062 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_228993327047 : Nat.Prime 228993327047 := by
  apply lucas_primality 228993327047 (5 : ZMod 228993327047)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (10408787593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (10408787593, 1)] : List FactorBlock).map factorBlockValue).prod) = 228993327047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_10408787593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 228993327047) ^ 114496663523 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 228993327047) ^ 20817575186 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 228993327047) ^ 22 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_239611493353 : Nat.Prime 239611493353 := by
  apply lucas_primality 239611493353 (10 : ZMod 239611493353)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (29, 1), (73, 2), (839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (29, 1), (73, 2), (839, 1)] : List FactorBlock).map factorBlockValue).prod) = 239611493353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_29
      · exact prime_oneHundredSixCZ_73
      · exact prime_oneHundredSixCZ_839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 239611493353) ^ 119805746676 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 239611493353) ^ 79870497784 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 239611493353) ^ 34230213336 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 239611493353) ^ 21782863032 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 239611493353) ^ 8262465288 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 239611493353) ^ 3282349224 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 239611493353) ^ 285591768 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_241123081229 : Nat.Prime 241123081229 := by
  apply lucas_primality 241123081229 (2 : ZMod 241123081229)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (157, 1), (173, 1), (47221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (157, 1), (173, 1), (47221, 1)] : List FactorBlock).map factorBlockValue).prod) = 241123081229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_47
      · exact prime_oneHundredSixCZ_157
      · exact prime_oneHundredSixCZ_173
      · exact prime_oneHundredSixCZ_47221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 241123081229) ^ 120561540614 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 241123081229) ^ 5130278324 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 241123081229) ^ 1535815804 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 241123081229) ^ 1393775036 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 241123081229) ^ 5106268 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_249324198001 : Nat.Prime 249324198001 := by
  apply lucas_primality 249324198001 (17 : ZMod 249324198001)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 3), (41, 1), (83, 1), (12211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 3), (41, 1), (83, 1), (12211, 1)] : List FactorBlock).map factorBlockValue).prod) = 249324198001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_83
      · exact prime_oneHundredSixCZ_12211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 249324198001) ^ 124662099000 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (17 : ZMod 249324198001) ^ 83108066000 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (17 : ZMod 249324198001) ^ 49864839600 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (17 : ZMod 249324198001) ^ 6081078000 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (17 : ZMod 249324198001) ^ 3003906000 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (17 : ZMod 249324198001) ^ 20418000 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_250137083873 : Nat.Prime 250137083873 := by
  apply lucas_primality 250137083873 (3 : ZMod 250137083873)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 2), (46253159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 2), (46253159, 1)] : List FactorBlock).map factorBlockValue).prod) = 250137083873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_46253159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 250137083873) ^ 125068541936 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 250137083873) ^ 19241314144 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 250137083873) ^ 5408 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_261456974479 : Nat.Prime 261456974479 := by
  apply lucas_primality 261456974479 (7 : ZMod 261456974479)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (2281, 1), (129959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (2281, 1), (129959, 1)] : List FactorBlock).map factorBlockValue).prod) = 261456974479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_2281
      · exact prime_oneHundredSixCZ_129959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 261456974479) ^ 130728487239 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 261456974479) ^ 87152324826 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 261456974479) ^ 37350996354 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 261456974479) ^ 114623838 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 261456974479) ^ 2011842 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_263206718813 : Nat.Prime 263206718813 := by
  apply lucas_primality 263206718813 (2 : ZMod 263206718813)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (157, 1), (1217, 1), (8009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (157, 1), (1217, 1), (8009, 1)] : List FactorBlock).map factorBlockValue).prod) = 263206718813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_43
      · exact prime_oneHundredSixCZ_157
      · exact prime_oneHundredSixCZ_1217
      · exact prime_oneHundredSixCZ_8009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 263206718813) ^ 131603359406 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 263206718813) ^ 6121086484 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 263206718813) ^ 1676475916 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 263206718813) ^ 216275036 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 263206718813) ^ 32863868 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_276188646443 : Nat.Prime 276188646443 := by
  apply lucas_primality 276188646443 (2 : ZMod 276188646443)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8837, 1), (15626833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8837, 1), (15626833, 1)] : List FactorBlock).map factorBlockValue).prod) = 276188646443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_8837
      · exact prime_oneHundredSixCZ_15626833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 276188646443) ^ 138094323221 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 276188646443) ^ 31253666 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 276188646443) ^ 17674 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_329614288063 : Nat.Prime 329614288063 := by
  apply lucas_primality 329614288063 (3 : ZMod 329614288063)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (78311, 1), (701507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (78311, 1), (701507, 1)] : List FactorBlock).map factorBlockValue).prod) = 329614288063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_78311
      · exact prime_oneHundredSixCZ_701507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 329614288063) ^ 164807144031 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 329614288063) ^ 109871429354 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 329614288063) ^ 4209042 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 329614288063) ^ 469866 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_341967428321 : Nat.Prime 341967428321 := by
  apply lucas_primality 341967428321 (3 : ZMod 341967428321)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (5527, 1), (55243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (5527, 1), (55243, 1)] : List FactorBlock).map factorBlockValue).prod) = 341967428321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_5527
      · exact prime_oneHundredSixCZ_55243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 341967428321) ^ 170983714160 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 341967428321) ^ 68393485664 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 341967428321) ^ 48852489760 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 341967428321) ^ 61872160 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 341967428321) ^ 6190240 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_387407651717 : Nat.Prime 387407651717 := by
  apply lucas_primality 387407651717 (2 : ZMod 387407651717)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (82237, 1), (1177717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (82237, 1), (1177717, 1)] : List FactorBlock).map factorBlockValue).prod) = 387407651717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_82237
      · exact prime_oneHundredSixCZ_1177717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 387407651717) ^ 193703825858 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 387407651717) ^ 4710868 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 387407651717) ^ 328948 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_449866622033 : Nat.Prime 449866622033 := by
  apply lucas_primality 449866622033 (3 : ZMod 449866622033)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (47, 1), (598226891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (47, 1), (598226891, 1)] : List FactorBlock).map factorBlockValue).prod) = 449866622033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_47
      · exact prime_oneHundredSixCZ_598226891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 449866622033) ^ 224933311016 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 449866622033) ^ 9571630256 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 449866622033) ^ 752 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_628179902447 : Nat.Prime 628179902447 := by
  apply lucas_primality 628179902447 (5 : ZMod 628179902447)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (1815548851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (1815548851, 1)] : List FactorBlock).map factorBlockValue).prod) = 628179902447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_173
      · exact prime_oneHundredSixCZ_1815548851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 628179902447) ^ 314089951223 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 628179902447) ^ 3631097702 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 628179902447) ^ 346 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_648470840627 : Nat.Prime 648470840627 := by
  apply lucas_primality 648470840627 (2 : ZMod 648470840627)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (267741883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (267741883, 1)] : List FactorBlock).map factorBlockValue).prod) = 648470840627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_173
      · exact prime_oneHundredSixCZ_267741883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 648470840627) ^ 324235420313 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 648470840627) ^ 92638691518 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 648470840627) ^ 3748386362 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 648470840627) ^ 2422 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_683934856643 : Nat.Prime 683934856643 := by
  apply lucas_primality 683934856643 (2 : ZMod 683934856643)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (341967428321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (341967428321, 1)] : List FactorBlock).map factorBlockValue).prod) = 683934856643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_341967428321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 683934856643) ^ 341967428321 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 683934856643) ^ 2 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_702194806871 : Nat.Prime 702194806871 := by
  apply lucas_primality 702194806871 (19 : ZMod 702194806871)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (4751, 1), (509653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (4751, 1), (509653, 1)] : List FactorBlock).map factorBlockValue).prod) = 702194806871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_29
      · exact prime_oneHundredSixCZ_4751
      · exact prime_oneHundredSixCZ_509653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 702194806871) ^ 351097403435 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (19 : ZMod 702194806871) ^ 140438961374 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (19 : ZMod 702194806871) ^ 24213614030 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (19 : ZMod 702194806871) ^ 147799370 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (19 : ZMod 702194806871) ^ 1377790 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_734139619601 : Nat.Prime 734139619601 := by
  apply lucas_primality 734139619601 (3 : ZMod 734139619601)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (59, 1), (31107611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (59, 1), (31107611, 1)] : List FactorBlock).map factorBlockValue).prod) = 734139619601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_59
      · exact prime_oneHundredSixCZ_31107611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 734139619601) ^ 367069809800 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 734139619601) ^ 146827923920 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 734139619601) ^ 12443044400 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 734139619601) ^ 23600 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_847809887167 : Nat.Prime 847809887167 := by
  apply lucas_primality 847809887167 (3 : ZMod 847809887167)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (23, 1), (186168179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (23, 1), (186168179, 1)] : List FactorBlock).map factorBlockValue).prod) = 847809887167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_23
      · exact prime_oneHundredSixCZ_186168179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 847809887167) ^ 423904943583 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 847809887167) ^ 282603295722 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 847809887167) ^ 77073626106 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 847809887167) ^ 36861299442 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 847809887167) ^ 4554 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_965573285387 : Nat.Prime 965573285387 := by
  apply lucas_primality 965573285387 (2 : ZMod 965573285387)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (55103, 1), (8761531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (55103, 1), (8761531, 1)] : List FactorBlock).map factorBlockValue).prod) = 965573285387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_55103
      · exact prime_oneHundredSixCZ_8761531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 965573285387) ^ 482786642693 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 965573285387) ^ 17523062 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 965573285387) ^ 110206 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1198484838211 : Nat.Prime 1198484838211 := by
  apply lucas_primality 1198484838211 (2 : ZMod 1198484838211)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (6311, 1), (33851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (6311, 1), (33851, 1)] : List FactorBlock).map factorBlockValue).prod) = 1198484838211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_6311
      · exact prime_oneHundredSixCZ_33851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1198484838211) ^ 599242419105 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 399494946070 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 239696967642 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 108953167110 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 70499108130 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 189904110 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198484838211) ^ 35404710 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1566517818589 : Nat.Prime 1566517818589 := by
  apply lucas_primality 1566517818589 (2 : ZMod 1566517818589)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (1948405247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (1948405247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1566517818589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_67
      · exact prime_oneHundredSixCZ_1948405247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1566517818589) ^ 783258909294 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1566517818589) ^ 522172606196 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1566517818589) ^ 23380862964 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1566517818589) ^ 804 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1654807199021 : Nat.Prime 1654807199021 := by
  apply lucas_primality 1654807199021 (3 : ZMod 1654807199021)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (53, 1), (293, 1), (5328119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (53, 1), (293, 1), (5328119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1654807199021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_53
      · exact prime_oneHundredSixCZ_293
      · exact prime_oneHundredSixCZ_5328119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1654807199021) ^ 827403599510 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654807199021) ^ 330961439804 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654807199021) ^ 31222777340 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654807199021) ^ 5647806140 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1654807199021) ^ 310580 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2167994435459 : Nat.Prime 2167994435459 := by
  apply lucas_primality 2167994435459 (2 : ZMod 2167994435459)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (11657, 1), (1754549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (11657, 1), (1754549, 1)] : List FactorBlock).map factorBlockValue).prod) = 2167994435459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_53
      · exact prime_oneHundredSixCZ_11657
      · exact prime_oneHundredSixCZ_1754549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2167994435459) ^ 1083997217729 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167994435459) ^ 40905555386 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167994435459) ^ 185982194 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167994435459) ^ 1235642 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2574700797673 : Nat.Prime 2574700797673 := by
  apply lucas_primality 2574700797673 (5 : ZMod 2574700797673)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11717, 1), (3051953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11717, 1), (3051953, 1)] : List FactorBlock).map factorBlockValue).prod) = 2574700797673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_11717
      · exact prime_oneHundredSixCZ_3051953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2574700797673) ^ 1287350398836 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2574700797673) ^ 858233599224 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2574700797673) ^ 219740616 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2574700797673) ^ 843624 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2711145119231 : Nat.Prime 2711145119231 := by
  apply lucas_primality 2711145119231 (17 : ZMod 2711145119231)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (421, 1), (643977463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (421, 1), (643977463, 1)] : List FactorBlock).map factorBlockValue).prod) = 2711145119231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_421
      · exact prime_oneHundredSixCZ_643977463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 2711145119231) ^ 1355572559615 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (17 : ZMod 2711145119231) ^ 542229023846 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (17 : ZMod 2711145119231) ^ 6439774630 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (17 : ZMod 2711145119231) ^ 4210 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_3379946058311 : Nat.Prime 3379946058311 := by
  apply lucas_primality 3379946058311 (7 : ZMod 3379946058311)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (5851, 1), (1863451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (5851, 1), (1863451, 1)] : List FactorBlock).map factorBlockValue).prod) = 3379946058311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_31
      · exact prime_oneHundredSixCZ_5851
      · exact prime_oneHundredSixCZ_1863451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3379946058311) ^ 1689973029155 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3379946058311) ^ 675989211662 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3379946058311) ^ 109030518010 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3379946058311) ^ 577669810 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3379946058311) ^ 1813810 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_4335988870919 : Nat.Prime 4335988870919 := by
  apply lucas_primality 4335988870919 (17 : ZMod 4335988870919)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2167994435459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2167994435459, 1)] : List FactorBlock).map factorBlockValue).prod) = 4335988870919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_2167994435459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 4335988870919) ^ 2167994435459 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (17 : ZMod 4335988870919) ^ 2 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_4595440430387 : Nat.Prime 4595440430387 := by
  apply lucas_primality 4595440430387 (2 : ZMod 4595440430387)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (59, 2), (127, 1), (173, 1), (2311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (59, 2), (127, 1), (173, 1), (2311, 1)] : List FactorBlock).map factorBlockValue).prod) = 4595440430387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_59
      · exact prime_oneHundredSixCZ_127
      · exact prime_oneHundredSixCZ_173
      · exact prime_oneHundredSixCZ_2311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4595440430387) ^ 2297720215193 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4595440430387) ^ 353495417722 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4595440430387) ^ 77888820854 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4595440430387) ^ 36184570318 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4595440430387) ^ 26563239482 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4595440430387) ^ 1988507326 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_6914126395331 : Nat.Prime 6914126395331 := by
  apply lucas_primality 6914126395331 (2 : ZMod 6914126395331)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (73, 1), (6373, 1), (19301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (73, 1), (6373, 1), (19301, 1)] : List FactorBlock).map factorBlockValue).prod) = 6914126395331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_73
      · exact prime_oneHundredSixCZ_6373
      · exact prime_oneHundredSixCZ_19301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6914126395331) ^ 3457063197665 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 1382825279066 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 987732342190 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 628556945030 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 94714060210 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 1084909210 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6914126395331) ^ 358226330 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_7998040021757 : Nat.Prime 7998040021757 := by
  apply lucas_primality 7998040021757 (2 : ZMod 7998040021757)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (461, 1), (3547, 1), (18251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (461, 1), (3547, 1), (18251, 1)] : List FactorBlock).map factorBlockValue).prod) = 7998040021757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_67
      · exact prime_oneHundredSixCZ_461
      · exact prime_oneHundredSixCZ_3547
      · exact prime_oneHundredSixCZ_18251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7998040021757) ^ 3999020010878 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7998040021757) ^ 119373731668 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7998040021757) ^ 17349327596 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7998040021757) ^ 2254874548 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7998040021757) ^ 438224756 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_9191779315207 : Nat.Prime 9191779315207 := by
  apply lucas_primality 9191779315207 (3 : ZMod 9191779315207)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (3119, 1), (21355273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (3119, 1), (21355273, 1)] : List FactorBlock).map factorBlockValue).prod) = 9191779315207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_23
      · exact prime_oneHundredSixCZ_3119
      · exact prime_oneHundredSixCZ_21355273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9191779315207) ^ 4595889657603 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9191779315207) ^ 3063926438402 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9191779315207) ^ 399642578922 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9191779315207) ^ 2947027674 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9191779315207) ^ 430422 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_13195542011621 : Nat.Prime 13195542011621 := by
  apply lucas_primality 13195542011621 (3 : ZMod 13195542011621)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (14207, 1), (46440283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (14207, 1), (46440283, 1)] : List FactorBlock).map factorBlockValue).prod) = 13195542011621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_14207
      · exact prime_oneHundredSixCZ_46440283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13195542011621) ^ 6597771005810 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13195542011621) ^ 2639108402324 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13195542011621) ^ 928805660 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13195542011621) ^ 284140 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_13448054836423 : Nat.Prime 13448054836423 := by
  apply lucas_primality 13448054836423 (7 : ZMod 13448054836423)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (49853, 1), (14986343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (49853, 1), (14986343, 1)] : List FactorBlock).map factorBlockValue).prod) = 13448054836423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_49853
      · exact prime_oneHundredSixCZ_14986343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 13448054836423) ^ 6724027418211 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 13448054836423) ^ 4482684945474 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 13448054836423) ^ 269754174 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 13448054836423) ^ 897354 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_13564958194673 : Nat.Prime 13564958194673 := by
  apply lucas_primality 13564958194673 (3 : ZMod 13564958194673)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (847809887167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (847809887167, 1)] : List FactorBlock).map factorBlockValue).prod) = 13564958194673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_847809887167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 13564958194673) ^ 6782479097336 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 13564958194673) ^ 16 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_17782306272719 : Nat.Prime 17782306272719 := by
  apply lucas_primality 17782306272719 (14 : ZMod 17782306272719)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (683934856643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (683934856643, 1)] : List FactorBlock).map factorBlockValue).prod) = 17782306272719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_683934856643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 17782306272719) ^ 8891153136359 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (14 : ZMod 17782306272719) ^ 1367869713286 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (14 : ZMod 17782306272719) ^ 26 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_19775651719609 : Nat.Prime 19775651719609 := by
  apply lucas_primality 19775651719609 (23 : ZMod 19775651719609)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (520837, 1), (527347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (520837, 1), (527347, 1)] : List FactorBlock).map factorBlockValue).prod) = 19775651719609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_520837
      · exact prime_oneHundredSixCZ_527347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 19775651719609) ^ 9887825859804 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (23 : ZMod 19775651719609) ^ 6591883906536 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (23 : ZMod 19775651719609) ^ 37968984 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (23 : ZMod 19775651719609) ^ 37500264 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_22244722109201 : Nat.Prime 22244722109201 := by
  apply lucas_primality 22244722109201 (6 : ZMod 22244722109201)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (71, 1), (783264863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (71, 1), (783264863, 1)] : List FactorBlock).map factorBlockValue).prod) = 22244722109201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_71
      · exact prime_oneHundredSixCZ_783264863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 22244722109201) ^ 11122361054600 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 22244722109201) ^ 4448944421840 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 22244722109201) ^ 313305945200 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 22244722109201) ^ 28400 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_23961149335301 : Nat.Prime 23961149335301 := by
  apply lucas_primality 23961149335301 (2 : ZMod 23961149335301)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (239611493353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (239611493353, 1)] : List FactorBlock).map factorBlockValue).prod) = 23961149335301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_239611493353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23961149335301) ^ 11980574667650 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23961149335301) ^ 4792229867060 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23961149335301) ^ 100 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_36698057394307 : Nat.Prime 36698057394307 := by
  apply lucas_primality 36698057394307 (3 : ZMod 36698057394307)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (14011, 1), (5669333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (14011, 1), (5669333, 1)] : List FactorBlock).map factorBlockValue).prod) = 36698057394307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_14011
      · exact prime_oneHundredSixCZ_5669333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36698057394307) ^ 18349028697153 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 36698057394307) ^ 12232685798102 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 36698057394307) ^ 5242579627758 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 36698057394307) ^ 3336187035846 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 36698057394307) ^ 2619231846 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 36698057394307) ^ 6473082 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_45846128675203 : Nat.Prime 45846128675203 := by
  apply lucas_primality 45846128675203 (5 : ZMod 45846128675203)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (827, 1), (9239445521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (827, 1), (9239445521, 1)] : List FactorBlock).map factorBlockValue).prod) = 45846128675203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_827
      · exact prime_oneHundredSixCZ_9239445521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 45846128675203) ^ 22923064337601 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 45846128675203) ^ 15282042891734 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 45846128675203) ^ 55436673126 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 45846128675203) ^ 4962 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_71479381476463 : Nat.Prime 71479381476463 := by
  apply lucas_primality 71479381476463 (5 : ZMod 71479381476463)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (811, 1), (14689556407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (811, 1), (14689556407, 1)] : List FactorBlock).map factorBlockValue).prod) = 71479381476463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_811
      · exact prime_oneHundredSixCZ_14689556407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 71479381476463) ^ 35739690738231 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 71479381476463) ^ 23826460492154 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 71479381476463) ^ 88137338442 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 71479381476463) ^ 4866 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_91496419386587 : Nat.Prime 91496419386587 := by
  apply lucas_primality 91496419386587 (2 : ZMod 91496419386587)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (487, 1), (325047851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (487, 1), (325047851, 1)] : List FactorBlock).map factorBlockValue).prod) = 91496419386587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_487
      · exact prime_oneHundredSixCZ_325047851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 91496419386587) ^ 45748209693293 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 91496419386587) ^ 5382142316858 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 91496419386587) ^ 187877657878 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 91496419386587) ^ 281486 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_122522352475447 : Nat.Prime 122522352475447 := by
  apply lucas_primality 122522352475447 (10 : ZMod 122522352475447)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (11, 1), (17, 1), (1733332661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (11, 1), (17, 1), (1733332661, 1)] : List FactorBlock).map factorBlockValue).prod) = 122522352475447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_1733332661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 122522352475447) ^ 61261176237723 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 122522352475447) ^ 40840784158482 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 122522352475447) ^ 17503193210778 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 122522352475447) ^ 11138395679586 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 122522352475447) ^ 7207197204438 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 122522352475447) ^ 70686 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_164238790852399 : Nat.Prime 164238790852399 := by
  apply lucas_primality 164238790852399 (6 : ZMod 164238790852399)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (1297, 1), (570404297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (1297, 1), (570404297, 1)] : List FactorBlock).map factorBlockValue).prod) = 164238790852399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_37
      · exact prime_oneHundredSixCZ_1297
      · exact prime_oneHundredSixCZ_570404297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 164238790852399) ^ 82119395426199 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 164238790852399) ^ 54746263617466 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 164238790852399) ^ 4438886239254 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 164238790852399) ^ 126629753934 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 164238790852399) ^ 287934 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_171540145210831 : Nat.Prime 171540145210831 := by
  apply lucas_primality 171540145210831 (11 : ZMod 171540145210831)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (109859, 1), (4731689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (109859, 1), (4731689, 1)] : List FactorBlock).map factorBlockValue).prod) = 171540145210831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_109859
      · exact prime_oneHundredSixCZ_4731689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 171540145210831) ^ 85770072605415 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 171540145210831) ^ 57180048403610 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 171540145210831) ^ 34308029042166 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 171540145210831) ^ 15594558655530 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 171540145210831) ^ 1561457370 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 171540145210831) ^ 36253470 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_225174899275231 : Nat.Prime 225174899275231 := by
  apply lucas_primality 225174899275231 (6 : ZMod 225174899275231)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (41, 1), (9635211779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (41, 1), (9635211779, 1)] : List FactorBlock).map factorBlockValue).prod) = 225174899275231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_9635211779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 225174899275231) ^ 112587449637615 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 225174899275231) ^ 75058299758410 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 225174899275231) ^ 45034979855046 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 225174899275231) ^ 11851310488170 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 225174899275231) ^ 5492070714030 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 225174899275231) ^ 23370 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_306139289307503 : Nat.Prime 306139289307503 := by
  apply lucas_primality 306139289307503 (5 : ZMod 306139289307503)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (71, 1), (3217, 1), (95737399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (71, 1), (3217, 1), (95737399, 1)] : List FactorBlock).map factorBlockValue).prod) = 306139289307503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_71
      · exact prime_oneHundredSixCZ_3217
      · exact prime_oneHundredSixCZ_95737399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 306139289307503) ^ 153069644653751 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 306139289307503) ^ 43734184186786 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 306139289307503) ^ 4311820976162 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 306139289307503) ^ 95162974606 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 306139289307503) ^ 3197698 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_405245070019753 : Nat.Prime 405245070019753 := by
  apply lucas_primality 405245070019753 (5 : ZMod 405245070019753)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (734139619601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (734139619601, 1)] : List FactorBlock).map factorBlockValue).prod) = 405245070019753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_23
      · exact prime_oneHundredSixCZ_734139619601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 405245070019753) ^ 202622535009876 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 405245070019753) ^ 135081690006584 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 405245070019753) ^ 17619350870424 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 405245070019753) ^ 552 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_489715526829241 : Nat.Prime 489715526829241 := by
  apply lucas_primality 489715526829241 (13 : ZMod 489715526829241)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (585367, 1), (2323877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (585367, 1), (2323877, 1)] : List FactorBlock).map factorBlockValue).prod) = 489715526829241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_585367
      · exact prime_oneHundredSixCZ_2323877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 489715526829241) ^ 244857763414620 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 489715526829241) ^ 163238508943080 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 489715526829241) ^ 97943105365848 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 489715526829241) ^ 836595720 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 489715526829241) ^ 210732120 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_649235870327489 : Nat.Prime 649235870327489 := by
  apply lucas_primality 649235870327489 (3 : ZMod 649235870327489)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (47, 1), (283, 1), (762672767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (47, 1), (283, 1), (762672767, 1)] : List FactorBlock).map factorBlockValue).prod) = 649235870327489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_47
      · exact prime_oneHundredSixCZ_283
      · exact prime_oneHundredSixCZ_762672767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 649235870327489) ^ 324617935163744 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 649235870327489) ^ 13813529155904 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 649235870327489) ^ 2294119683136 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 649235870327489) ^ 851264 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_953098149107887 : Nat.Prime 953098149107887 := by
  apply lucas_primality 953098149107887 (5 : ZMod 953098149107887)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4065767, 1), (39070043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4065767, 1), (39070043, 1)] : List FactorBlock).map factorBlockValue).prod) = 953098149107887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_4065767
      · exact prime_oneHundredSixCZ_39070043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 953098149107887) ^ 476549074553943 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 953098149107887) ^ 317699383035962 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 953098149107887) ^ 234420258 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 953098149107887) ^ 24394602 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1296322223320541 : Nat.Prime 1296322223320541 := by
  apply lucas_primality 1296322223320541 (2 : ZMod 1296322223320541)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (17, 1), (37, 1), (41, 1), (389, 1), (496999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (17, 1), (37, 1), (41, 1), (389, 1), (496999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1296322223320541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_37
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_389
      · exact prime_oneHundredSixCZ_496999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1296322223320541) ^ 648161111660270 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296322223320541) ^ 259264444664108 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296322223320541) ^ 99717094101580 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296322223320541) ^ 76254248430620 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296322223320541) ^ 35035735765420 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296322223320541) ^ 31617615202940 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296322223320541) ^ 3332447874860 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296322223320541) ^ 2608299460 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1530416088182323 : Nat.Prime 1530416088182323 := by
  apply lucas_primality 1530416088182323 (5 : ZMod 1530416088182323)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 2), (71, 1), (757, 1), (4357889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 2), (71, 1), (757, 1), (4357889, 1)] : List FactorBlock).map factorBlockValue).prod) = 1530416088182323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_71
      · exact prime_oneHundredSixCZ_757
      · exact prime_oneHundredSixCZ_4357889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1530416088182323) ^ 765208044091161 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1530416088182323) ^ 510138696060774 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1530416088182323) ^ 139128735289302 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1530416088182323) ^ 21555156171582 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1530416088182323) ^ 2021685717546 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1530416088182323) ^ 351182898 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2387432642262449 : Nat.Prime 2387432642262449 := by
  apply lucas_primality 2387432642262449 (3 : ZMod 2387432642262449)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (13564958194673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (13564958194673, 1)] : List FactorBlock).map factorBlockValue).prod) = 2387432642262449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_13564958194673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2387432642262449) ^ 1193716321131224 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2387432642262449) ^ 217039331114768 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2387432642262449) ^ 176 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2431642609582189 : Nat.Prime 2431642609582189 := by
  apply lucas_primality 2431642609582189 (6 : ZMod 2431642609582189)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (109, 1), (1103, 1), (27630367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (109, 1), (1103, 1), (27630367, 1)] : List FactorBlock).map factorBlockValue).prod) = 2431642609582189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_61
      · exact prime_oneHundredSixCZ_109
      · exact prime_oneHundredSixCZ_1103
      · exact prime_oneHundredSixCZ_27630367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2431642609582189) ^ 1215821304791094 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2431642609582189) ^ 810547536527396 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2431642609582189) ^ 39862993599708 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2431642609582189) ^ 22308647794332 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2431642609582189) ^ 2204571722196 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2431642609582189) ^ 88006164 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2671964329931387 : Nat.Prime 2671964329931387 := by
  apply lucas_primality 2671964329931387 (2 : ZMod 2671964329931387)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (109, 1), (250137083873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (109, 1), (250137083873, 1)] : List FactorBlock).map factorBlockValue).prod) = 2671964329931387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_109
      · exact prime_oneHundredSixCZ_250137083873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2671964329931387) ^ 1335982164965693 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2671964329931387) ^ 381709189990198 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2671964329931387) ^ 24513434219554 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2671964329931387) ^ 10682 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2733497752945097 : Nat.Prime 2733497752945097 := by
  apply lucas_primality 2733497752945097 (3 : ZMod 2733497752945097)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 2), (760187, 1), (1245091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 2), (760187, 1), (1245091, 1)] : List FactorBlock).map factorBlockValue).prod) = 2733497752945097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_760187
      · exact prime_oneHundredSixCZ_1245091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2733497752945097) ^ 1366748876472548 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2733497752945097) ^ 143868302786584 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2733497752945097) ^ 3595822808 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2733497752945097) ^ 2195420056 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_3244664082498463 : Nat.Prime 3244664082498463 := by
  apply lucas_primality 3244664082498463 (3 : ZMod 3244664082498463)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (31, 1), (397, 1), (1126682849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (31, 1), (397, 1), (1126682849, 1)] : List FactorBlock).map factorBlockValue).prod) = 3244664082498463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_31
      · exact prime_oneHundredSixCZ_397
      · exact prime_oneHundredSixCZ_1126682849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3244664082498463) ^ 1622332041249231 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3244664082498463) ^ 1081554694166154 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3244664082498463) ^ 249589544807574 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3244664082498463) ^ 104666583306402 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3244664082498463) ^ 8172957386646 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3244664082498463) ^ 2879838 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_3414902548338709 : Nat.Prime 3414902548338709 := by
  apply lucas_primality 3414902548338709 (2 : ZMod 3414902548338709)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (67, 1), (241, 1), (2517718571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (67, 1), (241, 1), (2517718571, 1)] : List FactorBlock).map factorBlockValue).prod) = 3414902548338709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_67
      · exact prime_oneHundredSixCZ_241
      · exact prime_oneHundredSixCZ_2517718571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3414902548338709) ^ 1707451274169354 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3414902548338709) ^ 1138300849446236 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3414902548338709) ^ 487843221191244 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3414902548338709) ^ 50968694751324 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3414902548338709) ^ 14169720117588 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3414902548338709) ^ 1356348 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_3463258354190329 : Nat.Prime 3463258354190329 := by
  apply lucas_primality 3463258354190329 (11 : ZMod 3463258354190329)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (307423, 1), (16185991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (307423, 1), (16185991, 1)] : List FactorBlock).map factorBlockValue).prod) = 3463258354190329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_29
      · exact prime_oneHundredSixCZ_307423
      · exact prime_oneHundredSixCZ_16185991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3463258354190329) ^ 1731629177095164 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 3463258354190329) ^ 1154419451396776 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 3463258354190329) ^ 119422701868632 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 3463258354190329) ^ 11265449736 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 3463258354190329) ^ 213966408 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_4031198682196039 : Nat.Prime 4031198682196039 := by
  apply lucas_primality 4031198682196039 (6 : ZMod 4031198682196039)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1292801, 1), (519698273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1292801, 1), (519698273, 1)] : List FactorBlock).map factorBlockValue).prod) = 4031198682196039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_1292801
      · exact prime_oneHundredSixCZ_519698273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4031198682196039) ^ 2015599341098019 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4031198682196039) ^ 1343732894065346 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4031198682196039) ^ 3118189638 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4031198682196039) ^ 7756806 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_4052450700197531 : Nat.Prime 4052450700197531 := by
  apply lucas_primality 4052450700197531 (6 : ZMod 4052450700197531)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (405245070019753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (405245070019753, 1)] : List FactorBlock).map factorBlockValue).prod) = 4052450700197531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_405245070019753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 4052450700197531) ^ 2026225350098765 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4052450700197531) ^ 810490140039506 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4052450700197531) ^ 10 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_4643916828201787 : Nat.Prime 4643916828201787 := by
  apply lucas_primality 4643916828201787 (2 : ZMod 4643916828201787)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (409, 1), (1877, 1), (1008197467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (409, 1), (1877, 1), (1008197467, 1)] : List FactorBlock).map factorBlockValue).prod) = 4643916828201787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_409
      · exact prime_oneHundredSixCZ_1877
      · exact prime_oneHundredSixCZ_1008197467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4643916828201787) ^ 2321958414100893 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4643916828201787) ^ 1547972276067262 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4643916828201787) ^ 11354319873354 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4643916828201787) ^ 2474116584018 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4643916828201787) ^ 4606158 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_5034423944422567 : Nat.Prime 5034423944422567 := by
  apply lucas_primality 5034423944422567 (3 : ZMod 5034423944422567)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (8630071, 1), (32408797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (8630071, 1), (32408797, 1)] : List FactorBlock).map factorBlockValue).prod) = 5034423944422567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_8630071
      · exact prime_oneHundredSixCZ_32408797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5034423944422567) ^ 2517211972211283 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5034423944422567) ^ 1678141314807522 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5034423944422567) ^ 583358346 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5034423944422567) ^ 155341278 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_6209783323944127 : Nat.Prime 6209783323944127 := by
  apply lucas_primality 6209783323944127 (5 : ZMod 6209783323944127)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (349, 1), (10433, 1), (284243513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (349, 1), (10433, 1), (284243513, 1)] : List FactorBlock).map factorBlockValue).prod) = 6209783323944127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_349
      · exact prime_oneHundredSixCZ_10433
      · exact prime_oneHundredSixCZ_284243513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6209783323944127) ^ 3104891661972063 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6209783323944127) ^ 2069927774648042 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6209783323944127) ^ 17793075426774 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6209783323944127) ^ 595205916222 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6209783323944127) ^ 21846702 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_6889926035597251 : Nat.Prime 6889926035597251 := by
  apply lucas_primality 6889926035597251 (10 : ZMod 6889926035597251)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (1453, 1), (6322483171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (1453, 1), (6322483171, 1)] : List FactorBlock).map factorBlockValue).prod) = 6889926035597251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_1453
      · exact prime_oneHundredSixCZ_6322483171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 6889926035597251) ^ 3444963017798625 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 6889926035597251) ^ 2296642011865750 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 6889926035597251) ^ 1377985207119450 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 6889926035597251) ^ 4741862378250 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (10 : ZMod 6889926035597251) ^ 1089750 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_8970785931444313 : Nat.Prime 8970785931444313 := by
  apply lucas_primality 8970785931444313 (13 : ZMod 8970785931444313)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13970293, 1), (26755541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13970293, 1), (26755541, 1)] : List FactorBlock).map factorBlockValue).prod) = 8970785931444313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_13970293
      · exact prime_oneHundredSixCZ_26755541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 8970785931444313) ^ 4485392965722156 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 8970785931444313) ^ 2990261977148104 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 8970785931444313) ^ 642132984 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 8970785931444313) ^ 335287032 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_10317485193027847 : Nat.Prime 10317485193027847 := by
  apply lucas_primality 10317485193027847 (6 : ZMod 10317485193027847)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8826157, 1), (194827813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8826157, 1), (194827813, 1)] : List FactorBlock).map factorBlockValue).prod) = 10317485193027847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_8826157
      · exact prime_oneHundredSixCZ_194827813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 10317485193027847) ^ 5158742596513923 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 10317485193027847) ^ 3439161731009282 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 10317485193027847) ^ 1168966878 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 10317485193027847) ^ 52956942 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_21163655729137391 : Nat.Prime 21163655729137391 := by
  apply lucas_primality 21163655729137391 (7 : ZMod 21163655729137391)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (193, 1), (1566517818589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (193, 1), (1566517818589, 1)] : List FactorBlock).map factorBlockValue).prod) = 21163655729137391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_193
      · exact prime_oneHundredSixCZ_1566517818589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 21163655729137391) ^ 10581827864568695 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 21163655729137391) ^ 4232731145827478 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 21163655729137391) ^ 3023379389876770 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 21163655729137391) ^ 109656247301230 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 21163655729137391) ^ 13510 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_32209181421770699 : Nat.Prime 32209181421770699 := by
  apply lucas_primality 32209181421770699 (2 : ZMod 32209181421770699)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (257, 1), (461, 1), (7995888361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (257, 1), (461, 1), (7995888361, 1)] : List FactorBlock).map factorBlockValue).prod) = 32209181421770699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_257
      · exact prime_oneHundredSixCZ_461
      · exact prime_oneHundredSixCZ_7995888361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32209181421770699) ^ 16104590710885349 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209181421770699) ^ 1894657730692394 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209181421770699) ^ 125327554170314 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209181421770699) ^ 69868072498418 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 32209181421770699) ^ 4028218 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_35777974856637683 : Nat.Prime 35777974856637683 := by
  apply lucas_primality 35777974856637683 (2 : ZMod 35777974856637683)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (6899, 1), (32822565421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (6899, 1), (32822565421, 1)] : List FactorBlock).map factorBlockValue).prod) = 35777974856637683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_79
      · exact prime_oneHundredSixCZ_6899
      · exact prime_oneHundredSixCZ_32822565421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35777974856637683) ^ 17888987428318841 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 35777974856637683) ^ 452885757678958 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 35777974856637683) ^ 5185965336518 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 35777974856637683) ^ 1090042 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_38007194700201613 : Nat.Prime 38007194700201613 := by
  apply lucas_primality 38007194700201613 (2 : ZMod 38007194700201613)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (83, 1), (479, 1), (2687, 1), (29648539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (83, 1), (479, 1), (2687, 1), (29648539, 1)] : List FactorBlock).map factorBlockValue).prod) = 38007194700201613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_83
      · exact prime_oneHundredSixCZ_479
      · exact prime_oneHundredSixCZ_2687
      · exact prime_oneHundredSixCZ_29648539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38007194700201613) ^ 19003597350100806 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38007194700201613) ^ 12669064900067204 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38007194700201613) ^ 457918008436164 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38007194700201613) ^ 79346961795828 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38007194700201613) ^ 14144843580276 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 38007194700201613) ^ 1281924708 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_50111080260518887 : Nat.Prime 50111080260518887 := by
  apply lucas_primality 50111080260518887 (6 : ZMod 50111080260518887)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (353, 1), (3379946058311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (353, 1), (3379946058311, 1)] : List FactorBlock).map factorBlockValue).prod) = 50111080260518887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_353
      · exact prime_oneHundredSixCZ_3379946058311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 50111080260518887) ^ 25055540130259443 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 50111080260518887) ^ 16703693420172962 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 50111080260518887) ^ 7158725751502698 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 50111080260518887) ^ 141957734449062 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 50111080260518887) ^ 14826 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_60344007327115289 : Nat.Prime 60344007327115289 := by
  apply lucas_primality 60344007327115289 (3 : ZMod 60344007327115289)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (31, 1), (1223, 1), (28422218221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (31, 1), (1223, 1), (28422218221, 1)] : List FactorBlock).map factorBlockValue).prod) = 60344007327115289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_31
      · exact prime_oneHundredSixCZ_1223
      · exact prime_oneHundredSixCZ_28422218221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 60344007327115289) ^ 30172003663557644 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 60344007327115289) ^ 8620572475302184 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 60344007327115289) ^ 1946580881519848 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 60344007327115289) ^ 49340970831656 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 60344007327115289) ^ 2123128 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_83561177395427257 : Nat.Prime 83561177395427257 := by
  apply lucas_primality 83561177395427257 (5 : ZMod 83561177395427257)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (503, 1), (329614288063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (503, 1), (329614288063, 1)] : List FactorBlock).map factorBlockValue).prod) = 83561177395427257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_503
      · exact prime_oneHundredSixCZ_329614288063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 83561177395427257) ^ 41780588697713628 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 83561177395427257) ^ 27853725798475752 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 83561177395427257) ^ 11937311056489608 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 83561177395427257) ^ 166125601183752 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 83561177395427257) ^ 253512 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_149246820764868341 : Nat.Prime 149246820764868341 := by
  apply lucas_primality 149246820764868341 (3 : ZMod 149246820764868341)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (659, 1), (276188646443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (659, 1), (276188646443, 1)] : List FactorBlock).map factorBlockValue).prod) = 149246820764868341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_659
      · exact prime_oneHundredSixCZ_276188646443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 149246820764868341) ^ 74623410382434170 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 149246820764868341) ^ 29849364152973668 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 149246820764868341) ^ 3640166360118740 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 149246820764868341) ^ 226474690083260 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 149246820764868341) ^ 540380 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_220885006180777541 : Nat.Prime 220885006180777541 := by
  apply lucas_primality 220885006180777541 (3 : ZMod 220885006180777541)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (203897, 1), (1105425109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (203897, 1), (1105425109, 1)] : List FactorBlock).map factorBlockValue).prod) = 220885006180777541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_203897
      · exact prime_oneHundredSixCZ_1105425109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 220885006180777541) ^ 110442503090388770 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 220885006180777541) ^ 44177001236155508 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 220885006180777541) ^ 31555000882968220 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 220885006180777541) ^ 1083316606820 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 220885006180777541) ^ 199819060 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_298493641529736683 : Nat.Prime 298493641529736683 := by
  apply lucas_primality 298493641529736683 (2 : ZMod 298493641529736683)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149246820764868341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149246820764868341, 1)] : List FactorBlock).map factorBlockValue).prod) = 298493641529736683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_149246820764868341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 298493641529736683) ^ 149246820764868341 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 298493641529736683) ^ 2 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_427786333695778531 : Nat.Prime 427786333695778531 := by
  apply lucas_primality 427786333695778531 (2 : ZMod 427786333695778531)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (1296322223320541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (1296322223320541, 1)] : List FactorBlock).map factorBlockValue).prod) = 427786333695778531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_1296322223320541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 427786333695778531) ^ 213893166847889265 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 427786333695778531) ^ 142595444565259510 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 427786333695778531) ^ 85557266739155706 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 427786333695778531) ^ 38889666699616230 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 427786333695778531) ^ 330 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_447361700242105757 : Nat.Prime 447361700242105757 := by
  apply lucas_primality 447361700242105757 (2 : ZMod 447361700242105757)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (119270369, 1), (937705031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (119270369, 1), (937705031, 1)] : List FactorBlock).map factorBlockValue).prod) = 447361700242105757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_119270369
      · exact prime_oneHundredSixCZ_937705031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 447361700242105757) ^ 223680850121052878 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 447361700242105757) ^ 3750820124 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 447361700242105757) ^ 477081476 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_512488460647336399 : Nat.Prime 512488460647336399 := by
  apply lucas_primality 512488460647336399 (3 : ZMod 512488460647336399)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6473, 1), (13195542011621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6473, 1), (13195542011621, 1)] : List FactorBlock).map factorBlockValue).prod) = 512488460647336399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_6473
      · exact prime_oneHundredSixCZ_13195542011621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 512488460647336399) ^ 256244230323668199 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 512488460647336399) ^ 170829486882445466 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 512488460647336399) ^ 79173252069726 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 512488460647336399) ^ 38838 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_551013665718067483 : Nat.Prime 551013665718067483 := by
  apply lucas_primality 551013665718067483 (3 : ZMod 551013665718067483)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (204443, 1), (64171299547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (204443, 1), (64171299547, 1)] : List FactorBlock).map factorBlockValue).prod) = 551013665718067483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_204443
      · exact prime_oneHundredSixCZ_64171299547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 551013665718067483) ^ 275506832859033741 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 551013665718067483) ^ 183671221906022494 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 551013665718067483) ^ 78716237959723926 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 551013665718067483) ^ 2695194580974 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 551013665718067483) ^ 8586606 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_810284163285790201 : Nat.Prime 810284163285790201 := by
  apply lucas_primality 810284163285790201 (11 : ZMod 810284163285790201)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (7, 1), (25127, 1), (7677987853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (7, 1), (25127, 1), (7677987853, 1)] : List FactorBlock).map factorBlockValue).prod) = 810284163285790201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_25127
      · exact prime_oneHundredSixCZ_7677987853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 810284163285790201) ^ 405142081642895100 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 810284163285790201) ^ 270094721095263400 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 810284163285790201) ^ 162056832657158040 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 810284163285790201) ^ 115754880469398600 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 810284163285790201) ^ 32247548982600 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 810284163285790201) ^ 105533400 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1557062618130853969 : Nat.Prime 1557062618130853969 := by
  apply lucas_primality 1557062618130853969 (23 : ZMod 1557062618130853969)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (14593, 1), (19889, 1), (111765383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (14593, 1), (19889, 1), (111765383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1557062618130853969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_14593
      · exact prime_oneHundredSixCZ_19889
      · exact prime_oneHundredSixCZ_111765383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1557062618130853969) ^ 778531309065426984 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1557062618130853969) ^ 519020872710284656 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1557062618130853969) ^ 106699281719376 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1557062618130853969) ^ 78287627237712 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1557062618130853969) ^ 13931528496 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1723072164228297137 : Nat.Prime 1723072164228297137 := by
  apply lucas_primality 1723072164228297137 (3 : ZMod 1723072164228297137)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (151, 1), (277, 1), (2574700797673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (151, 1), (277, 1), (2574700797673, 1)] : List FactorBlock).map factorBlockValue).prod) = 1723072164228297137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_151
      · exact prime_oneHundredSixCZ_277
      · exact prime_oneHundredSixCZ_2574700797673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1723072164228297137) ^ 861536082114148568 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1723072164228297137) ^ 11411073935286736 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1723072164228297137) ^ 6220477127177968 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1723072164228297137) ^ 669232 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1925676806392616047 : Nat.Prime 1925676806392616047 := by
  apply lucas_primality 1925676806392616047 (5 : ZMod 1925676806392616047)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (1823, 1), (19687, 1), (116138233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (1823, 1), (19687, 1), (116138233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1925676806392616047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_1823
      · exact prime_oneHundredSixCZ_19687
      · exact prime_oneHundredSixCZ_116138233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1925676806392616047) ^ 962838403196308023 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925676806392616047) ^ 641892268797538682 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925676806392616047) ^ 275096686627516578 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925676806392616047) ^ 175061527853874186 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925676806392616047) ^ 1056322987598802 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925676806392616047) ^ 97814639426658 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925676806392616047) ^ 16580903262 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1957807607855321821 : Nat.Prime 1957807607855321821 := by
  apply lucas_primality 1957807607855321821 (2 : ZMod 1957807607855321821)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 2), (31, 1), (229, 1), (27197869187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 2), (31, 1), (229, 1), (27197869187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1957807607855321821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_31
      · exact prime_oneHundredSixCZ_229
      · exact prime_oneHundredSixCZ_27197869187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1957807607855321821) ^ 978903803927660910 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 652602535951773940 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 391561521571064364 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 150600585219640140 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 63155084124365220 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 8549378200241580 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1957807607855321821) ^ 71983860 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_101
      · exact prime_oneHundredSixCZ_191
      · exact prime_oneHundredSixCZ_48017
      · exact prime_oneHundredSixCZ_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_3005535128788957469 : Nat.Prime 3005535128788957469 := by
  apply lucas_primality 3005535128788957469 (2 : ZMod 3005535128788957469)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (6209783323944127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (6209783323944127, 1)] : List FactorBlock).map factorBlockValue).prod) = 3005535128788957469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_6209783323944127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3005535128788957469) ^ 1502767564394478734 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3005535128788957469) ^ 273230466253541588 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3005535128788957469) ^ 484 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_4103392498243839653 : Nat.Prime 4103392498243839653 := by
  apply lucas_primality 4103392498243839653 (2 : ZMod 4103392498243839653)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (60344007327115289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (60344007327115289, 1)] : List FactorBlock).map factorBlockValue).prod) = 4103392498243839653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_60344007327115289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4103392498243839653) ^ 2051696249121919826 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103392498243839653) ^ 241376029308461156 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103392498243839653) ^ 68 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_5924407526678798057 : Nat.Prime 5924407526678798057 := by
  apply lucas_primality 5924407526678798057 (3 : ZMod 5924407526678798057)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (59, 1), (306139289307503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (59, 1), (306139289307503, 1)] : List FactorBlock).map factorBlockValue).prod) = 5924407526678798057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_59
      · exact prime_oneHundredSixCZ_306139289307503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5924407526678798057) ^ 2962203763339399028 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5924407526678798057) ^ 144497744553141416 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5924407526678798057) ^ 100413686892860984 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5924407526678798057) ^ 19352 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_8947234004842115141 : Nat.Prime 8947234004842115141 := by
  apply lucas_primality 8947234004842115141 (3 : ZMod 8947234004842115141)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (447361700242105757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (447361700242105757, 1)] : List FactorBlock).map factorBlockValue).prod) = 8947234004842115141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_447361700242105757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8947234004842115141) ^ 4473617002421057570 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8947234004842115141) ^ 1789446800968423028 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8947234004842115141) ^ 20 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_11172125489077444261 : Nat.Prime 11172125489077444261 := by
  apply lucas_primality 11172125489077444261 (2 : ZMod 11172125489077444261)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (409, 1), (23961149335301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (409, 1), (23961149335301, 1)] : List FactorBlock).map factorBlockValue).prod) = 11172125489077444261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_409
      · exact prime_oneHundredSixCZ_23961149335301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11172125489077444261) ^ 5586062744538722130 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172125489077444261) ^ 3724041829692481420 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172125489077444261) ^ 2234425097815488852 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172125489077444261) ^ 588006604688286540 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172125489077444261) ^ 27315710242243140 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11172125489077444261) ^ 466260 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_12561721862134067009 : Nat.Prime 12561721862134067009 := by
  apply lucas_primality 12561721862134067009 (3 : ZMod 12561721862134067009)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (353, 1), (5743, 1), (7321, 1), (13224683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (353, 1), (5743, 1), (7321, 1), (13224683, 1)] : List FactorBlock).map factorBlockValue).prod) = 12561721862134067009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_353
      · exact prime_oneHundredSixCZ_5743
      · exact prime_oneHundredSixCZ_7321
      · exact prime_oneHundredSixCZ_13224683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12561721862134067009) ^ 6280860931067033504 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 12561721862134067009) ^ 35585614340323136 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 12561721862134067009) ^ 2187310092657856 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 12561721862134067009) ^ 1715847816163648 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 12561721862134067009) ^ 949869411776 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_13098604310793702893 : Nat.Prime 13098604310793702893 := by
  apply lucas_primality 13098604310793702893 (2 : ZMod 13098604310793702893)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17757281, 1), (184411739483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17757281, 1), (184411739483, 1)] : List FactorBlock).map factorBlockValue).prod) = 13098604310793702893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_17757281
      · exact prime_oneHundredSixCZ_184411739483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13098604310793702893) ^ 6549302155396851446 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13098604310793702893) ^ 737646957932 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13098604310793702893) ^ 71029124 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_15020180420292872789 : Nat.Prime 15020180420292872789 := by
  apply lucas_primality 15020180420292872789 (2 : ZMod 15020180420292872789)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (220885006180777541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (220885006180777541, 1)] : List FactorBlock).map factorBlockValue).prod) = 15020180420292872789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_220885006180777541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15020180420292872789) ^ 7510090210146436394 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15020180420292872789) ^ 883540024723110164 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15020180420292872789) ^ 68 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_16715643925665254249 : Nat.Prime 16715643925665254249 := by
  apply lucas_primality 16715643925665254249 (3 : ZMod 16715643925665254249)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (298493641529736683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (298493641529736683, 1)] : List FactorBlock).map factorBlockValue).prod) = 16715643925665254249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_298493641529736683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16715643925665254249) ^ 8357821962832627124 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 16715643925665254249) ^ 2387949132237893464 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 16715643925665254249) ^ 56 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_22317101458347153313 : Nat.Prime 22317101458347153313 := by
  apply lucas_primality 22317101458347153313 (5 : ZMod 22317101458347153313)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11913173, 1), (6504558913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11913173, 1), (6504558913, 1)] : List FactorBlock).map factorBlockValue).prod) = 22317101458347153313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_11913173
      · exact prime_oneHundredSixCZ_6504558913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 22317101458347153313) ^ 11158550729173576656 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 22317101458347153313) ^ 7439033819449051104 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 22317101458347153313) ^ 1873312966944 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 22317101458347153313) ^ 3430993824 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_28082145087567908317 : Nat.Prime 28082145087567908317 := by
  apply lucas_primality 28082145087567908317 (13 : ZMod 28082145087567908317)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (139, 1), (389, 1), (228993327047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (139, 1), (389, 1), (228993327047, 1)] : List FactorBlock).map factorBlockValue).prod) = 28082145087567908317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_139
      · exact prime_oneHundredSixCZ_389
      · exact prime_oneHundredSixCZ_228993327047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 28082145087567908317) ^ 14041072543783954158 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 28082145087567908317) ^ 9360715029189302772 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 28082145087567908317) ^ 4011735012509701188 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 28082145087567908317) ^ 202029820773869844 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 28082145087567908317) ^ 72190604338220844 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 28082145087567908317) ^ 122633028 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_308579586981309408937 : Nat.Prime 308579586981309408937 := by
  apply lucas_primality 308579586981309408937 (5 : ZMod 308579586981309408937)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (32272609, 1), (10767630683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (32272609, 1), (10767630683, 1)] : List FactorBlock).map factorBlockValue).prod) = 308579586981309408937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_37
      · exact prime_oneHundredSixCZ_32272609
      · exact prime_oneHundredSixCZ_10767630683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 308579586981309408937) ^ 154289793490654704468 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 308579586981309408937) ^ 102859862327103136312 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 308579586981309408937) ^ 8339988837332686728 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 308579586981309408937) ^ 9561656046504 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 308579586981309408937) ^ 28658076792 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_342017481667622015413 : Nat.Prime 342017481667622015413 := by
  apply lucas_primality 342017481667622015413 (2 : ZMod 342017481667622015413)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4057, 1), (145517, 1), (16092631393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4057, 1), (145517, 1), (16092631393, 1)] : List FactorBlock).map factorBlockValue).prod) = 342017481667622015413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_4057
      · exact prime_oneHundredSixCZ_145517
      · exact prime_oneHundredSixCZ_16092631393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 342017481667622015413) ^ 171008740833811007706 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 342017481667622015413) ^ 114005827222540671804 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 342017481667622015413) ^ 84303051926946516 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 342017481667622015413) ^ 2350361000210436 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 342017481667622015413) ^ 21253048884 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_391443298283670903773 : Nat.Prime 391443298283670903773 := by
  apply lucas_primality 391443298283670903773 (2 : ZMod 391443298283670903773)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (188983, 1), (2711145119231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (188983, 1), (2711145119231, 1)] : List FactorBlock).map factorBlockValue).prod) = 391443298283670903773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_191
      · exact prime_oneHundredSixCZ_188983
      · exact prime_oneHundredSixCZ_2711145119231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 391443298283670903773) ^ 195721649141835451886 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 391443298283670903773) ^ 2049441352270528292 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 391443298283670903773) ^ 2071314871092484 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 391443298283670903773) ^ 144383012 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_417686148190500523487 : Nat.Prime 417686148190500523487 := by
  apply lucas_primality 417686148190500523487 (5 : ZMod 417686148190500523487)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (269, 1), (547, 1), (1861583, 1), (762426647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (269, 1), (547, 1), (1861583, 1), (762426647, 1)] : List FactorBlock).map factorBlockValue).prod) = 417686148190500523487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_269
      · exact prime_oneHundredSixCZ_547
      · exact prime_oneHundredSixCZ_1861583
      · exact prime_oneHundredSixCZ_762426647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 417686148190500523487) ^ 208843074095250261743 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 417686148190500523487) ^ 1552736610373607894 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 417686148190500523487) ^ 763594420823584138 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 417686148190500523487) ^ 224371488239042 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 417686148190500523487) ^ 547837814738 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_688098984484206390301 : Nat.Prime 688098984484206390301 := by
  apply lucas_primality 688098984484206390301 (2 : ZMod 688098984484206390301)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (4457, 1), (171540145210831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (4457, 1), (171540145210831, 1)] : List FactorBlock).map factorBlockValue).prod) = 688098984484206390301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_4457
      · exact prime_oneHundredSixCZ_171540145210831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 688098984484206390301) ^ 344049492242103195150 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 688098984484206390301) ^ 229366328161402130100 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 688098984484206390301) ^ 137619796896841278060 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 688098984484206390301) ^ 154386130689747900 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 688098984484206390301) ^ 4011300 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_853906360559472657461 : Nat.Prime 853906360559472657461 := by
  apply lucas_primality 853906360559472657461 (2 : ZMod 853906360559472657461)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (29, 2), (2671964329931387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (29, 2), (2671964329931387, 1)] : List FactorBlock).map factorBlockValue).prod) = 853906360559472657461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_29
      · exact prime_oneHundredSixCZ_2671964329931387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 853906360559472657461) ^ 426953180279736328730 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 853906360559472657461) ^ 170781272111894531492 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 853906360559472657461) ^ 44942440029445929340 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 853906360559472657461) ^ 29445046915843884740 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 853906360559472657461) ^ 319580 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1231588058715079810753 : Nat.Prime 1231588058715079810753 := by
  apply lucas_primality 1231588058715079810753 (5 : ZMod 1231588058715079810753)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 2), (19, 1), (6889926035597251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 2), (19, 1), (6889926035597251, 1)] : List FactorBlock).map factorBlockValue).prod) = 1231588058715079810753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_6889926035597251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1231588058715079810753) ^ 615794029357539905376 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231588058715079810753) ^ 410529352905026603584 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231588058715079810753) ^ 175941151245011401536 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231588058715079810753) ^ 64820424142898937408 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1231588058715079810753) ^ 178752 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1876391059039720275781 : Nat.Prime 1876391059039720275781 := by
  apply lucas_primality 1876391059039720275781 (2 : ZMod 1876391059039720275781)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (13, 1), (17, 1), (127, 1), (283, 1), (35963, 1), (5213321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (13, 1), (17, 1), (127, 1), (283, 1), (35963, 1), (5213321, 1)] : List FactorBlock).map factorBlockValue).prod) = 1876391059039720275781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_13
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_127
      · exact prime_oneHundredSixCZ_283
      · exact prime_oneHundredSixCZ_35963
      · exact prime_oneHundredSixCZ_5213321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1876391059039720275781) ^ 938195529519860137890 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876391059039720275781) ^ 625463686346573425260 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876391059039720275781) ^ 375278211807944055156 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876391059039720275781) ^ 268055865577102896540 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876391059039720275781) ^ 144337773772286175060 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876391059039720275781) ^ 110375944649395310340 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876391059039720275781) ^ 14774732748344254140 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876391059039720275781) ^ 6630357099080283660 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876391059039720275781) ^ 52175598783186060 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876391059039720275781) ^ 359922410118180 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_3255241225360649277199 : Nat.Prime 3255241225360649277199 := by
  apply lucas_primality 3255241225360649277199 (6 : ZMod 3255241225360649277199)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (83, 2), (443, 1), (4335988870919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (83, 2), (443, 1), (4335988870919, 1)] : List FactorBlock).map factorBlockValue).prod) = 3255241225360649277199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_83
      · exact prime_oneHundredSixCZ_443
      · exact prime_oneHundredSixCZ_4335988870919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3255241225360649277199) ^ 1627620612680324638599 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3255241225360649277199) ^ 1085080408453549759066 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3255241225360649277199) ^ 79396127447820714078 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3255241225360649277199) ^ 39219773799525894906 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3255241225360649277199) ^ 7348174323613203786 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3255241225360649277199) ^ 750749442 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_4375454987258216338523 : Nat.Prime 4375454987258216338523 := by
  apply lucas_primality 4375454987258216338523 (2 : ZMod 4375454987258216338523)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (397, 1), (1367, 1), (4031198682196039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (397, 1), (1367, 1), (4031198682196039, 1)] : List FactorBlock).map factorBlockValue).prod) = 4375454987258216338523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_397
      · exact prime_oneHundredSixCZ_1367
      · exact prime_oneHundredSixCZ_4031198682196039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4375454987258216338523) ^ 2187727493629108169261 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4375454987258216338523) ^ 11021297197123970626 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4375454987258216338523) ^ 3200771753663654966 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4375454987258216338523) ^ 1085398 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_9834697860361674440251 : Nat.Prime 9834697860361674440251 := by
  apply lucas_primality 9834697860361674440251 (3 : ZMod 9834697860361674440251)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (11, 1), (82699231, 1), (14414699807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (11, 1), (82699231, 1), (14414699807, 1)] : List FactorBlock).map factorBlockValue).prod) = 9834697860361674440251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_82699231
      · exact prime_oneHundredSixCZ_14414699807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9834697860361674440251) ^ 4917348930180837220125 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9834697860361674440251) ^ 3278232620120558146750 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9834697860361674440251) ^ 1966939572072334888050 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9834697860361674440251) ^ 894063441851061312750 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9834697860361674440251) ^ 118921273407750 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9834697860361674440251) ^ 682268655750 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_10193628030468171081431 : Nat.Prime 10193628030468171081431 := by
  apply lucas_primality 10193628030468171081431 (13 : ZMod 10193628030468171081431)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (1109, 1), (83561177395427257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (1109, 1), (83561177395427257, 1)] : List FactorBlock).map factorBlockValue).prod) = 10193628030468171081431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_1109
      · exact prime_oneHundredSixCZ_83561177395427257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 10193628030468171081431) ^ 5096814015234085540715 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 10193628030468171081431) ^ 2038725606093634216286 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 10193628030468171081431) ^ 926693457315288280130 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 10193628030468171081431) ^ 9191729513496998270 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (13 : ZMod 10193628030468171081431) ^ 121990 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_23980393550586262495571 : Nat.Prime 23980393550586262495571 := by
  apply lucas_primality 23980393550586262495571 (2 : ZMod 23980393550586262495571)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (59, 1), (197, 1), (2156117, 1), (5628813031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (59, 1), (197, 1), (2156117, 1), (5628813031, 1)] : List FactorBlock).map factorBlockValue).prod) = 23980393550586262495571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_59
      · exact prime_oneHundredSixCZ_197
      · exact prime_oneHundredSixCZ_2156117
      · exact prime_oneHundredSixCZ_5628813031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23980393550586262495571) ^ 11990196775293131247785 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 4796078710117252499114 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 1410611385328603676210 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 406447348315021398230 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 121727886043585088810 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 11122027956083210 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23980393550586262495571) ^ 4260293141470 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_31487486244331769929873 : Nat.Prime 31487486244331769929873 := by
  apply lucas_primality 31487486244331769929873 (11 : ZMod 31487486244331769929873)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (151, 1), (15383, 1), (13448054836423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (151, 1), (15383, 1), (13448054836423, 1)] : List FactorBlock).map factorBlockValue).prod) = 31487486244331769929873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_151
      · exact prime_oneHundredSixCZ_15383
      · exact prime_oneHundredSixCZ_13448054836423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 31487486244331769929873) ^ 15743743122165884964936 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 31487486244331769929873) ^ 10495828748110589976624 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 31487486244331769929873) ^ 4498212320618824275696 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 31487486244331769929873) ^ 208526398969084569072 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 31487486244331769929873) ^ 2046901530542271984 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 31487486244331769929873) ^ 2341415664 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_54792035898450103080757 : Nat.Prime 54792035898450103080757 := by
  apply lucas_primality 54792035898450103080757 (5 : ZMod 54792035898450103080757)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (149491, 1), (49983169, 1), (203692999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (149491, 1), (49983169, 1), (203692999, 1)] : List FactorBlock).map factorBlockValue).prod) = 54792035898450103080757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_149491
      · exact prime_oneHundredSixCZ_49983169
      · exact prime_oneHundredSixCZ_203692999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54792035898450103080757) ^ 27396017949225051540378 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 54792035898450103080757) ^ 18264011966150034360252 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 54792035898450103080757) ^ 366523977352817916 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 54792035898450103080757) ^ 1096209724086324 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 54792035898450103080757) ^ 268993221011244 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_98735001851394535958543 : Nat.Prime 98735001851394535958543 := by
  apply lucas_primality 98735001851394535958543 (5 : ZMod 98735001851394535958543)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (96329, 1), (512488460647336399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (96329, 1), (512488460647336399, 1)] : List FactorBlock).map factorBlockValue).prod) = 98735001851394535958543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_96329
      · exact prime_oneHundredSixCZ_512488460647336399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 98735001851394535958543) ^ 49367500925697267979271 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 98735001851394535958543) ^ 1024976921294672798 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 98735001851394535958543) ^ 192658 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_158573863103064139659323 : Nat.Prime 158573863103064139659323 := by
  apply lucas_primality 158573863103064139659323 (2 : ZMod 158573863103064139659323)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (503, 1), (127363, 1), (6914126395331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (503, 1), (127363, 1), (6914126395331, 1)] : List FactorBlock).map factorBlockValue).prod) = 158573863103064139659323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_179
      · exact prime_oneHundredSixCZ_503
      · exact prime_oneHundredSixCZ_127363
      · exact prime_oneHundredSixCZ_6914126395331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158573863103064139659323) ^ 79286931551532069829661 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 158573863103064139659323) ^ 885887503369073405918 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 158573863103064139659323) ^ 315256189071698090774 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 158573863103064139659323) ^ 1245054396512834494 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 158573863103064139659323) ^ 22934764862 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_275180638401134749306021 : Nat.Prime 275180638401134749306021 := by
  apply lucas_primality 275180638401134749306021 (6 : ZMod 275180638401134749306021)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (61, 1), (101, 1), (487, 1), (360511, 1), (4240020271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (61, 1), (101, 1), (487, 1), (360511, 1), (4240020271, 1)] : List FactorBlock).map factorBlockValue).prod) = 275180638401134749306021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_61
      · exact prime_oneHundredSixCZ_101
      · exact prime_oneHundredSixCZ_487
      · exact prime_oneHundredSixCZ_360511
      · exact prime_oneHundredSixCZ_4240020271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 275180638401134749306021) ^ 137590319200567374653010 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 275180638401134749306021) ^ 91726879467044916435340 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 275180638401134749306021) ^ 55036127680226949861204 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 275180638401134749306021) ^ 4511158006575979496820 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 275180638401134749306021) ^ 2724560776248858904020 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 275180638401134749306021) ^ 565052645587545686460 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 275180638401134749306021) ^ 763307190075017820 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 275180638401134749306021) ^ 64900783678620 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_776337554374472215060891 : Nat.Prime 776337554374472215060891 := by
  apply lucas_primality 776337554374472215060891 (3 : ZMod 776337554374472215060891)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (71, 1), (97159, 1), (91496419386587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (71, 1), (97159, 1), (91496419386587, 1)] : List FactorBlock).map factorBlockValue).prod) = 776337554374472215060891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_71
      · exact prime_oneHundredSixCZ_97159
      · exact prime_oneHundredSixCZ_91496419386587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 776337554374472215060891) ^ 388168777187236107530445 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 776337554374472215060891) ^ 258779184791490738353630 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 776337554374472215060891) ^ 155267510874894443012178 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 776337554374472215060891) ^ 18935062301816395489290 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 776337554374472215060891) ^ 10934331751753129789590 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 776337554374472215060891) ^ 7990382305030642710 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 776337554374472215060891) ^ 8484895470 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1054698157016850365812477 : Nat.Prime 1054698157016850365812477 := by
  apply lucas_primality 1054698157016850365812477 (5 : ZMod 1054698157016850365812477)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (3255241225360649277199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (3255241225360649277199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1054698157016850365812477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_3255241225360649277199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1054698157016850365812477) ^ 527349078508425182906238 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1054698157016850365812477) ^ 351566052338950121937492 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1054698157016850365812477) ^ 324 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1968556725701751108468361 : Nat.Prime 1968556725701751108468361 := by
  apply lucas_primality 1968556725701751108468361 (7 : ZMod 1968556725701751108468361)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (404191, 1), (2387432642262449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (404191, 1), (2387432642262449, 1)] : List FactorBlock).map factorBlockValue).prod) = 1968556725701751108468361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_404191
      · exact prime_oneHundredSixCZ_2387432642262449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1968556725701751108468361) ^ 984278362850875554234180 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1968556725701751108468361) ^ 656185575233917036156120 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1968556725701751108468361) ^ 393711345140350221693672 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1968556725701751108468361) ^ 115797454453044182851080 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1968556725701751108468361) ^ 4870362590215395960 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1968556725701751108468361) ^ 824549640 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2270541901563560845675333 : Nat.Prime 2270541901563560845675333 := by
  apply lucas_primality 2270541901563560845675333 (2 : ZMod 2270541901563560845675333)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (151, 1), (417686148190500523487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (151, 1), (417686148190500523487, 1)] : List FactorBlock).map factorBlockValue).prod) = 2270541901563560845675333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_151
      · exact prime_oneHundredSixCZ_417686148190500523487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2270541901563560845675333) ^ 1135270950781780422837666 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2270541901563560845675333) ^ 756847300521186948558444 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2270541901563560845675333) ^ 15036701334858018845532 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2270541901563560845675333) ^ 5436 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2350078567957453724565959 : Nat.Prime 2350078567957453724565959 := by
  apply lucas_primality 2350078567957453724565959 (7 : ZMod 2350078567957453724565959)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (23980393550586262495571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (23980393550586262495571, 1)] : List FactorBlock).map factorBlockValue).prod) = 2350078567957453724565959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_23980393550586262495571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2350078567957453724565959) ^ 1175039283978726862282979 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2350078567957453724565959) ^ 335725509708207674937994 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2350078567957453724565959) ^ 98 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2393984291948100735772223 : Nat.Prime 2393984291948100735772223 := by
  apply lucas_primality 2393984291948100735772223 (5 : ZMod 2393984291948100735772223)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (563, 1), (3803, 1), (9281, 1), (1369793, 1), (1911961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (563, 1), (3803, 1), (9281, 1), (1369793, 1), (1911961, 1)] : List FactorBlock).map factorBlockValue).prod) = 2393984291948100735772223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_23
      · exact prime_oneHundredSixCZ_563
      · exact prime_oneHundredSixCZ_3803
      · exact prime_oneHundredSixCZ_9281
      · exact prime_oneHundredSixCZ_1369793
      · exact prime_oneHundredSixCZ_1911961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2393984291948100735772223) ^ 1196992145974050367886111 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 104086273562960901555314 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 4252192348042807701194 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 629498893491480603674 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 257944649493384412862 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 1747697857959633854 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2393984291948100735772223) ^ 1252109374588760302 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_3872451941007946891916579 : Nat.Prime 3872451941007946891916579 := by
  apply lucas_primality 3872451941007946891916579 (2 : ZMod 3872451941007946891916579)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (41, 1), (823, 1), (34589, 1), (4595440430387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (41, 1), (823, 1), (34589, 1), (4595440430387, 1)] : List FactorBlock).map factorBlockValue).prod) = 3872451941007946891916579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_19
      · exact prime_oneHundredSixCZ_41
      · exact prime_oneHundredSixCZ_823
      · exact prime_oneHundredSixCZ_34589
      · exact prime_oneHundredSixCZ_4595440430387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3872451941007946891916579) ^ 1936225970503973445958289 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872451941007946891916579) ^ 203813260053049836416662 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872451941007946891916579) ^ 94450047341657241266258 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872451941007946891916579) ^ 4705287899159109224686 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872451941007946891916579) ^ 111956169331520046602 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3872451941007946891916579) ^ 842672644694 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_3875086262056251617693393 : Nat.Prime 3875086262056251617693393 := by
  apply lucas_primality 3875086262056251617693393 (3 : ZMod 3875086262056251617693393)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (131, 1), (35831, 1), (1493719, 1), (34543175743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (131, 1), (35831, 1), (1493719, 1), (34543175743, 1)] : List FactorBlock).map factorBlockValue).prod) = 3875086262056251617693393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_131
      · exact prime_oneHundredSixCZ_35831
      · exact prime_oneHundredSixCZ_1493719
      · exact prime_oneHundredSixCZ_34543175743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3875086262056251617693393) ^ 1937543131028125808846696 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3875086262056251617693393) ^ 29580811160734745173232 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3875086262056251617693393) ^ 108148984456371622832 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3875086262056251617693393) ^ 2594253846979419568 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3875086262056251617693393) ^ 112180949744944 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_4475564791075289358101651 : Nat.Prime 4475564791075289358101651 := by
  apply lucas_primality 4475564791075289358101651 (2 : ZMod 4475564791075289358101651)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (83, 1), (2521, 1), (427786333695778531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (83, 1), (2521, 1), (427786333695778531, 1)] : List FactorBlock).map factorBlockValue).prod) = 4475564791075289358101651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_83
      · exact prime_oneHundredSixCZ_2521
      · exact prime_oneHundredSixCZ_427786333695778531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4475564791075289358101651) ^ 2237782395537644679050825 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4475564791075289358101651) ^ 895112958215057871620330 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4475564791075289358101651) ^ 53922467362352883832550 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4475564791075289358101651) ^ 1775313284837480903650 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4475564791075289358101651) ^ 10462150 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_13027057142920912402931843 : Nat.Prime 13027057142920912402931843 := by
  apply lucas_primality 13027057142920912402931843 (2 : ZMod 13027057142920912402931843)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (39521, 1), (425422253, 1), (387407651717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (39521, 1), (425422253, 1), (387407651717, 1)] : List FactorBlock).map factorBlockValue).prod) = 13027057142920912402931843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_39521
      · exact prime_oneHundredSixCZ_425422253
      · exact prime_oneHundredSixCZ_387407651717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13027057142920912402931843) ^ 6513528571460456201465921 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13027057142920912402931843) ^ 329623672045770916802 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13027057142920912402931843) ^ 30621475607015114 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13027057142920912402931843) ^ 33626225721626 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_20890196651925183749992387 : Nat.Prime 20890196651925183749992387 := by
  apply lucas_primality 20890196651925183749992387 (2 : ZMod 20890196651925183749992387)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (257, 1), (1231588058715079810753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (257, 1), (1231588058715079810753, 1)] : List FactorBlock).map factorBlockValue).prod) = 20890196651925183749992387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_257
      · exact prime_oneHundredSixCZ_1231588058715079810753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20890196651925183749992387) ^ 10445098325962591874996193 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20890196651925183749992387) ^ 6963398883975061249997462 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20890196651925183749992387) ^ 1899108786538653068181126 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20890196651925183749992387) ^ 81284811875195267509698 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 20890196651925183749992387) ^ 16962 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_31535050255384795499799781 : Nat.Prime 31535050255384795499799781 := by
  apply lucas_primality 31535050255384795499799781 (7 : ZMod 31535050255384795499799781)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (83, 1), (51635320351, 1), (122635811411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (83, 1), (51635320351, 1), (122635811411, 1)] : List FactorBlock).map factorBlockValue).prod) = 31535050255384795499799781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_83
      · exact prime_oneHundredSixCZ_51635320351
      · exact prime_oneHundredSixCZ_122635811411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 31535050255384795499799781) ^ 15767525127692397749899890 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 31535050255384795499799781) ^ 10511683418461598499933260 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 31535050255384795499799781) ^ 6307010051076959099959956 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 31535050255384795499799781) ^ 379940364522708379515660 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 31535050255384795499799781) ^ 610726340826780 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (7 : ZMod 31535050255384795499799781) ^ 257143895347980 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_64498347768862160224500427 : Nat.Prime 64498347768862160224500427 := by
  apply lucas_primality 64498347768862160224500427 (2 : ZMod 64498347768862160224500427)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (17409451, 1), (85754447, 1), (313060141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (17409451, 1), (85754447, 1), (313060141, 1)] : List FactorBlock).map factorBlockValue).prod) = 64498347768862160224500427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_23
      · exact prime_oneHundredSixCZ_17409451
      · exact prime_oneHundredSixCZ_85754447
      · exact prime_oneHundredSixCZ_313060141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64498347768862160224500427) ^ 32249173884431080112250213 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64498347768862160224500427) ^ 21499449256287386741500142 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64498347768862160224500427) ^ 2804275989950528705413062 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64498347768862160224500427) ^ 3704789299149189726 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64498347768862160224500427) ^ 752128315501377558 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64498347768862160224500427) ^ 206025422344846386 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_348111915874719936989456471 : Nat.Prime 348111915874719936989456471 := by
  apply lucas_primality 348111915874719936989456471 (11 : ZMod 348111915874719936989456471)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 2), (7603, 1), (127277, 1), (17782306272719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 2), (7603, 1), (127277, 1), (17782306272719, 1)] : List FactorBlock).map factorBlockValue).prod) = 348111915874719936989456471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_17
      · exact prime_oneHundredSixCZ_7603
      · exact prime_oneHundredSixCZ_127277
      · exact prime_oneHundredSixCZ_17782306272719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 348111915874719936989456471) ^ 174055957937359968494728235 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 348111915874719936989456471) ^ 69622383174943987397891294 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 348111915874719936989456471) ^ 49730273696388562427065210 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 348111915874719936989456471) ^ 20477171522042349234673910 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 348111915874719936989456471) ^ 45786125986415880177490 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 348111915874719936989456471) ^ 2735073232985692128110 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (11 : ZMod 348111915874719936989456471) ^ 19576308637130 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_413598315890756360779552243 : Nat.Prime 413598315890756360779552243 := by
  apply lucas_primality 413598315890756360779552243 (2 : ZMod 413598315890756360779552243)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (59, 1), (67, 1), (4523, 1), (749659, 1), (34985897161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (59, 1), (67, 1), (4523, 1), (749659, 1), (34985897161, 1)] : List FactorBlock).map factorBlockValue).prod) = 413598315890756360779552243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_59
      · exact prime_oneHundredSixCZ_67
      · exact prime_oneHundredSixCZ_4523
      · exact prime_oneHundredSixCZ_749659
      · exact prime_oneHundredSixCZ_34985897161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 413598315890756360779552243) ^ 206799157945378180389776121 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 413598315890756360779552243) ^ 137866105296918786926517414 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 413598315890756360779552243) ^ 59085473698679480111364606 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 413598315890756360779552243) ^ 7010140947300955267450038 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 413598315890756360779552243) ^ 6173109192399348668351526 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 413598315890756360779552243) ^ 91443359692849073796054 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 413598315890756360779552243) ^ 551715267729402782838 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 413598315890756360779552243) ^ 11821858218682722 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_1989210947855542497082608407 : Nat.Prime 1989210947855542497082608407 := by
  apply lucas_primality 1989210947855542497082608407 (5 : ZMod 1989210947855542497082608407)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (530063, 1), (1876391059039720275781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (530063, 1), (1876391059039720275781, 1)] : List FactorBlock).map factorBlockValue).prod) = 1989210947855542497082608407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_530063
      · exact prime_oneHundredSixCZ_1876391059039720275781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1989210947855542497082608407) ^ 994605473927771248541304203 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1989210947855542497082608407) ^ 3752782118079440551562 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1989210947855542497082608407) ^ 1060126 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2784895326997759495915651769 : Nat.Prime 2784895326997759495915651769 := by
  apply lucas_primality 2784895326997759495915651769 (3 : ZMod 2784895326997759495915651769)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (348111915874719936989456471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (348111915874719936989456471, 1)] : List FactorBlock).map factorBlockValue).prod) = 2784895326997759495915651769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_348111915874719936989456471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2784895326997759495915651769) ^ 1392447663498879747957825884 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2784895326997759495915651769) ^ 8 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_2983816421783313745623912611 : Nat.Prime 2983816421783313745623912611 := by
  apply lucas_primality 2983816421783313745623912611 (2 : ZMod 2983816421783313745623912611)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (3875086262056251617693393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (3875086262056251617693393, 1)] : List FactorBlock).map factorBlockValue).prod) = 2983816421783313745623912611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_3875086262056251617693393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2983816421783313745623912611) ^ 1491908210891656872811956305 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2983816421783313745623912611) ^ 596763284356662749124782522 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2983816421783313745623912611) ^ 426259488826187677946273230 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2983816421783313745623912611) ^ 271256038343937613238537510 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2983816421783313745623912611) ^ 770 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_5221678738120799054841847069 : Nat.Prime 5221678738120799054841847069 := by
  apply lucas_primality 5221678738120799054841847069 (2 : ZMod 5221678738120799054841847069)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (701, 1), (3613, 1), (5924407526678798057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (701, 1), (3613, 1), (5924407526678798057, 1)] : List FactorBlock).map factorBlockValue).prod) = 5221678738120799054841847069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_3
      · exact prime_oneHundredSixCZ_29
      · exact prime_oneHundredSixCZ_701
      · exact prime_oneHundredSixCZ_3613
      · exact prime_oneHundredSixCZ_5924407526678798057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5221678738120799054841847069) ^ 2610839369060399527420923534 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5221678738120799054841847069) ^ 1740559579373599684947282356 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5221678738120799054841847069) ^ 180057887521406863960063692 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5221678738120799054841847069) ^ 7448899769073893088219468 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5221678738120799054841847069) ^ 1445247367318239428409036 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5221678738120799054841847069) ^ 881384124 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_7832518107181198582262770601 : Nat.Prime 7832518107181198582262770601 := by
  apply lucas_primality 7832518107181198582262770601 (6 : ZMod 7832518107181198582262770601)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 7832518107181198582262770601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_53
      · exact prime_oneHundredSixCZ_171401
      · exact prime_oneHundredSixCZ_714027719
      · exact prime_oneHundredSixCZ_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7832518107181198582262770601) ^ 3916259053590599291131385300 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 7832518107181198582262770601) ^ 1566503621436239716452554120 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 7832518107181198582262770601) ^ 147783360512852803438920200 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 7832518107181198582262770601) ^ 45697038565592957930600 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 7832518107181198582262770601) ^ 10969487456524357400 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (6 : ZMod 7832518107181198582262770601) ^ 1297281689681781400 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_8354685980993278487746955309 : Nat.Prime 8354685980993278487746955309 := by
  apply lucas_primality 8354685980993278487746955309 (3 : ZMod 8354685980993278487746955309)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (11, 1), (3875086262056251617693393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (11, 1), (3875086262056251617693393, 1)] : List FactorBlock).map factorBlockValue).prod) = 8354685980993278487746955309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_7
      · exact prime_oneHundredSixCZ_11
      · exact prime_oneHundredSixCZ_3875086262056251617693393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8354685980993278487746955309) ^ 4177342990496639243873477654 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8354685980993278487746955309) ^ 1193526568713325498249565044 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8354685980993278487746955309) ^ 759516907363025317067905028 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8354685980993278487746955309) ^ 2156 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_11392753610445379756018575419 : Nat.Prime 11392753610445379756018575419 := by
  apply lucas_primality 11392753610445379756018575419 (2 : ZMod 11392753610445379756018575419)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1471, 1), (3872451941007946891916579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1471, 1), (3872451941007946891916579, 1)] : List FactorBlock).map factorBlockValue).prod) = 11392753610445379756018575419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_1471
      · exact prime_oneHundredSixCZ_3872451941007946891916579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11392753610445379756018575419) ^ 5696376805222689878009287709 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11392753610445379756018575419) ^ 7744903882015893783833158 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11392753610445379756018575419) ^ 2942 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixCZ_125320289714899177316204329601 : Nat.Prime 125320289714899177316204329601 := by
  apply lucas_primality 125320289714899177316204329601 (3 : ZMod 125320289714899177316204329601)
  · rw [← oneHundredSixCZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 2), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 2), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixCZ_2
      · exact prime_oneHundredSixCZ_5
      · exact prime_oneHundredSixCZ_53
      · exact prime_oneHundredSixCZ_171401
      · exact prime_oneHundredSixCZ_714027719
      · exact prime_oneHundredSixCZ_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 125320289714899177316204329601) ^ 62660144857449588658102164800 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 125320289714899177316204329601) ^ 25064057942979835463240865920 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 125320289714899177316204329601) ^ 2364533768205644855022723200 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 125320289714899177316204329601) ^ 731152617049487326889600 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 125320289714899177316204329601) ^ 175511799304389718400 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide
    · change (3 : ZMod 125320289714899177316204329601) ^ 20756507034908502400 ≠ 1
      rw [← oneHundredSixCZFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329600 : Nat.totient 125320289714899177316204329600 = 49182015358737949156724736000 := by
  rw [← show ((([(2, 7), (5, 2), (53, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_53, prime_oneHundredSixCZ_171401, prime_oneHundredSixCZ_714027719, prime_oneHundredSixCZ_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329601 : Nat.totient 125320289714899177316204329601 = 125320289714899177316204329600 := by
  rw [← show ((([(125320289714899177316204329601, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_125320289714899177316204329601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329602 : Nat.totient 125320289714899177316204329602 = 41768888821163265317043407472 := by
  rw [← show ((([(2, 1), (3, 1), (9199, 1), (2270541901563560845675333, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_9199, prime_oneHundredSixCZ_2270541901563560845675333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329603 : Nat.totient 125320289714899177316204329603 = 120942279489689090879483068416 := by
  rw [← show ((([(29, 1), (2137, 1), (16504544513, 1), (122522352475447, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_29, prime_oneHundredSixCZ_2137, prime_oneHundredSixCZ_16504544513, prime_oneHundredSixCZ_122522352475447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329604 : Nat.totient 125320289714899177316204329604 = 59830455424366933588419372224 := by
  rw [← show ((([(2, 2), (23, 1), (569, 1), (2393984291948100735772223, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_23, prime_oneHundredSixCZ_569, prime_oneHundredSixCZ_2393984291948100735772223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329605 : Nat.totient 125320289714899177316204329605 = 66837487847946227901975642432 := by
  rw [← show ((([(3, 2), (5, 1), (2784895326997759495915651769, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_2784895326997759495915651769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329606 : Nat.totient 125320289714899177316204329606 = 53693167161806575955223120000 := by
  rw [← show ((([(2, 1), (7, 1), (4349, 1), (21487, 1), (145543, 1), (172751, 1), (3809923631, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_4349, prime_oneHundredSixCZ_21487, prime_oneHundredSixCZ_145543, prime_oneHundredSixCZ_172751, prime_oneHundredSixCZ_3809923631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329607 : Nat.totient 125320289714899177316204329607 = 125288299349597627490057451200 := by
  rw [← show ((([(3931, 1), (1135241, 1), (28082145087567908317, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3931, prime_oneHundredSixCZ_1135241, prime_oneHundredSixCZ_28082145087567908317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329608 : Nat.totient 125320289714899177316204329608 = 36048279151493364740474351616 := by
  rw [← show ((([(2, 3), (3, 1), (13, 1), (17, 1), (149, 1), (158573863103064139659323, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_13, prime_oneHundredSixCZ_17, prime_oneHundredSixCZ_149, prime_oneHundredSixCZ_158573863103064139659323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329609 : Nat.totient 125320289714899177316204329609 = 113927536104453797560185754180 := by
  rw [← show ((([(11, 1), (11392753610445379756018575419, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_11, prime_oneHundredSixCZ_11392753610445379756018575419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329610 : Nat.totient 125320289714899177316204329610 = 48440499722397164441877891840 := by
  rw [← show ((([(2, 1), (5, 1), (47, 1), (79, 1), (1723957, 1), (1957807607855321821, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_47, prime_oneHundredSixCZ_79, prime_oneHundredSixCZ_1723957, prime_oneHundredSixCZ_1957807607855321821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329611 : Nat.totient 125320289714899177316204329611 = 83528722678892264523076158720 := by
  rw [← show ((([(3, 1), (7417, 1), (12227, 1), (2045653, 1), (225174899275231, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_7417, prime_oneHundredSixCZ_12227, prime_oneHundredSixCZ_2045653, prime_oneHundredSixCZ_225174899275231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329612 : Nat.totient 125320289714899177316204329612 = 59362242495769294843880820240 := by
  rw [← show ((([(2, 2), (19, 1), (77914288607, 1), (21163655729137391, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_19, prime_oneHundredSixCZ_77914288607, prime_oneHundredSixCZ_21163655729137391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329613 : Nat.totient 125320289714899177316204329613 = 107292050004287743739960894496 := by
  rw [← show ((([(7, 1), (857, 1), (20890196651925183749992387, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_857, prime_oneHundredSixCZ_20890196651925183749992387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329614 : Nat.totient 125320289714899177316204329614 = 40425896899216086060482346240 := by
  rw [← show ((([(2, 1), (3, 2), (31, 1), (13435817, 1), (16715643925665254249, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_31, prime_oneHundredSixCZ_13435817, prime_oneHundredSixCZ_16715643925665254249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329615 : Nat.totient 125320289714899177316204329615 = 100078156647241355512157016096 := by
  rw [← show ((([(5, 1), (563, 1), (888401383, 1), (50111080260518887, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_563, prime_oneHundredSixCZ_888401383, prime_oneHundredSixCZ_50111080260518887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329616 : Nat.totient 125320289714899177316204329616 = 62660144857449588658102164800 := by
  rw [← show ((([(2, 4), (7832518107181198582262770601, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_7832518107181198582262770601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329617 : Nat.totient 125320289714899177316204329617 = 83544750413618751176737848912 := by
  rw [← show ((([(3, 1), (39607, 1), (1054698157016850365812477, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_39607, prime_oneHundredSixCZ_1054698157016850365812477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329618 : Nat.totient 125320289714899177316204329618 = 62659552499897583675844895760 := by
  rw [← show ((([(2, 1), (126047, 1), (678499, 1), (21696511, 1), (33769121923, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_126047, prime_oneHundredSixCZ_678499, prime_oneHundredSixCZ_21696511, prime_oneHundredSixCZ_33769121923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329619 : Nat.totient 125320289714899177316204329619 = 125320258227412932984430419744 := by
  rw [← show ((([(3980003, 1), (31487486244331769929873, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3980003, prime_oneHundredSixCZ_31487486244331769929873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329620 : Nat.totient 125320289714899177316204329620 = 26040579681018010870899594240 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (7, 2), (11, 1), (3875086262056251617693393, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_11, prime_oneHundredSixCZ_3875086262056251617693393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329621 : Nat.totient 125320289714899177316204329621 = 112349469449250339262506241920 := by
  rw [← show ((([(13, 1), (59, 1), (83, 1), (1968556725701751108468361, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_13, prime_oneHundredSixCZ_59, prime_oneHundredSixCZ_83, prime_oneHundredSixCZ_1968556725701751108468361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329622 : Nat.totient 125320289714899177316204329622 = 62194912032531317296897267200 := by
  rw [← show ((([(2, 1), (191, 1), (457, 1), (80233, 1), (8947234004842115141, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_191, prime_oneHundredSixCZ_457, prime_oneHundredSixCZ_80233, prime_oneHundredSixCZ_8947234004842115141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329623 : Nat.totient 125320289714899177316204329623 = 81288827491037304402947828736 := by
  rw [← show ((([(3, 5), (37, 1), (8951737, 1), (1557062618130853969, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_37, prime_oneHundredSixCZ_8951737, prime_oneHundredSixCZ_1557062618130853969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329624 : Nat.totient 125320289714899177316204329624 = 62014061436769909101672483840 := by
  rw [← show ((([(2, 3), (97, 1), (604907, 1), (2312752087, 1), (115436188111, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_97, prime_oneHundredSixCZ_604907, prime_oneHundredSixCZ_2312752087, prime_oneHundredSixCZ_115436188111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329625 : Nat.totient 125320289714899177316204329625 = 93537696185513663925452800000 := by
  rw [← show ((([(5, 3), (17, 1), (227, 1), (233, 1), (43481, 1), (1017311, 1), (25207362881, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_17, prime_oneHundredSixCZ_227, prime_oneHundredSixCZ_233, prime_oneHundredSixCZ_43481, prime_oneHundredSixCZ_1017311, prime_oneHundredSixCZ_25207362881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329626 : Nat.totient 125320289714899177316204329626 = 40749852614664204219560563200 := by
  rw [← show ((([(2, 1), (3, 1), (41, 1), (8647, 1), (35601920213, 1), (1654807199021, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_41, prime_oneHundredSixCZ_8647, prime_oneHundredSixCZ_35601920213, prime_oneHundredSixCZ_1654807199021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329627 : Nat.totient 125320289714899177316204329627 = 102006668469335875123076700480 := by
  rw [← show ((([(7, 1), (23, 2), (139, 1), (84067, 1), (264766231, 1), (10938675403, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_23, prime_oneHundredSixCZ_139, prime_oneHundredSixCZ_84067, prime_oneHundredSixCZ_264766231, prime_oneHundredSixCZ_10938675403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329628 : Nat.totient 125320289714899177316204329628 = 61176447941973048307103754240 := by
  rw [← show ((([(2, 2), (73, 1), (103, 1), (2417, 1), (1438441219, 1), (1198484838211, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_73, prime_oneHundredSixCZ_103, prime_oneHundredSixCZ_2417, prime_oneHundredSixCZ_1438441219, prime_oneHundredSixCZ_1198484838211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329629 : Nat.totient 125320289714899177316204329629 = 82719663178151272155910448400 := by
  rw [← show ((([(3, 1), (101, 1), (413598315890756360779552243, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_101, prime_oneHundredSixCZ_413598315890756360779552243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329630 : Nat.totient 125320289714899177316204329630 = 50127819834021016331157422080 := by
  rw [← show ((([(2, 1), (5, 1), (195281, 1), (1818233, 1), (4255697, 1), (8293563323, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_195281, prime_oneHundredSixCZ_1818233, prime_oneHundredSixCZ_4255697, prime_oneHundredSixCZ_8293563323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329631 : Nat.totient 125320289714899177316204329631 = 107881817478780867117932080800 := by
  rw [← show ((([(11, 1), (19, 1), (2179, 1), (275180638401134749306021, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_11, prime_oneHundredSixCZ_19, prime_oneHundredSixCZ_2179, prime_oneHundredSixCZ_275180638401134749306021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329632 : Nat.totient 125320289714899177316204329632 = 40264283110342161036876595200 := by
  rw [← show ((([(2, 5), (3, 2), (29, 1), (701, 1), (3613, 1), (5924407526678798057, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_29, prime_oneHundredSixCZ_701, prime_oneHundredSixCZ_3613, prime_oneHundredSixCZ_5924407526678798057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329633 : Nat.totient 125320289714899177316204329633 = 122461806227516662313599360000 := by
  rw [← show ((([(71, 1), (113, 1), (702194806871, 1), (22244722109201, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_71, prime_oneHundredSixCZ_113, prime_oneHundredSixCZ_702194806871, prime_oneHundredSixCZ_22244722109201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329634 : Nat.totient 125320289714899177316204329634 = 49408051812737507105274700992 := by
  rw [← show ((([(2, 1), (7, 1), (13, 1), (293, 1), (2350078567957453724565959, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_13, prime_oneHundredSixCZ_293, prime_oneHundredSixCZ_2350078567957453724565959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329635 : Nat.totient 125320289714899177316204329635 = 66837487847946227901975642464 := by
  rw [← show ((([(3, 1), (5, 1), (8354685980993278487746955309, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_8354685980993278487746955309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329636 : Nat.totient 125320289714899177316204329636 = 61202931131161473427965983232 := by
  rw [← show ((([(2, 2), (43, 1), (58002107, 1), (12561721862134067009, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_43, prime_oneHundredSixCZ_58002107, prime_oneHundredSixCZ_12561721862134067009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329637 : Nat.totient 125320289714899177316204329637 = 124350810731720334367626136480 := by
  rw [← show ((([(131, 1), (9689, 1), (98735001851394535958543, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_131, prime_oneHundredSixCZ_9689, prime_oneHundredSixCZ_98735001851394535958543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329638 : Nat.totient 125320289714899177316204329638 = 41773429904901972778949553896 := by
  rw [← show ((([(2, 1), (3, 1), (648470840627, 1), (32209181421770699, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_648470840627, prime_oneHundredSixCZ_32209181421770699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329639 : Nat.totient 125320289714899177316204329639 = 125295980767705133045380805760 := by
  rw [← show ((([(5233, 1), (348911, 1), (71083819, 1), (965573285387, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_5233, prime_oneHundredSixCZ_348911, prime_oneHundredSixCZ_71083819, prime_oneHundredSixCZ_965573285387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329640 : Nat.totient 125320289714899177316204329640 = 49946217949141848158069597184 := by
  rw [← show ((([(2, 3), (5, 1), (283, 1), (18743, 1), (47527, 1), (47533, 1), (261456974479, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_283, prime_oneHundredSixCZ_18743, prime_oneHundredSixCZ_47527, prime_oneHundredSixCZ_47533, prime_oneHundredSixCZ_261456974479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329641 : Nat.totient 125320289714899177316204329641 = 71611594122799529894973902616 := by
  rw [← show ((([(3, 2), (7, 1), (1989210947855542497082608407, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_1989210947855542497082608407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329642 : Nat.totient 125320289714899177316204329642 = 53612958166247650269979476480 := by
  rw [← show ((([(2, 1), (11, 1), (17, 1), (96753101927, 1), (3463258354190329, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_11, prime_oneHundredSixCZ_17, prime_oneHundredSixCZ_96753101927, prime_oneHundredSixCZ_3463258354190329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329643 : Nat.totient 125320289714899177316204329643 = 125320234922863278866098961688 := by
  rw [← show ((([(2287199, 1), (54792035898450103080757, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2287199, prime_oneHundredSixCZ_54792035898450103080757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329644 : Nat.totient 125320289714899177316204329644 = 41586102438271079708560833600 := by
  rw [← show ((([(2, 2), (3, 1), (223, 1), (15581651, 1), (3005535128788957469, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_223, prime_oneHundredSixCZ_15581651, prime_oneHundredSixCZ_3005535128788957469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329645 : Nat.totient 125320289714899177316204329645 = 97022159778200277311231748480 := by
  rw [← show ((([(5, 1), (31, 1), (90127888943, 1), (8970785931444313, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_31, prime_oneHundredSixCZ_90127888943, prime_oneHundredSixCZ_8970785931444313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329646 : Nat.totient 125320289714899177316204329646 = 61632816876901167829900416000 := by
  rw [← show ((([(2, 1), (61, 1), (559841, 1), (25669421, 1), (71479381476463, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_61, prime_oneHundredSixCZ_559841, prime_oneHundredSixCZ_25669421, prime_oneHundredSixCZ_71479381476463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329647 : Nat.totient 125320289714899177316204329647 = 77000609867728283655332069376 := by
  rw [← show ((([(3, 1), (13, 1), (673, 1), (15473, 1), (308579586981309408937, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_13, prime_oneHundredSixCZ_673, prime_oneHundredSixCZ_15473, prime_oneHundredSixCZ_308579586981309408937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329648 : Nat.totient 125320289714899177316204329648 = 53705506037203187917013472768 := by
  rw [← show ((([(2, 4), (7, 1), (16843, 1), (69702169, 1), (953098149107887, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_16843, prime_oneHundredSixCZ_69702169, prime_oneHundredSixCZ_953098149107887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329649 : Nat.totient 125320289714899177316204329649 = 124693422171937757816832000000 := by
  rw [← show ((([(281, 1), (691, 1), (1004659, 1), (2576641, 1), (249324198001, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_281, prime_oneHundredSixCZ_691, prime_oneHundredSixCZ_1004659, prime_oneHundredSixCZ_2576641, prime_oneHundredSixCZ_249324198001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329650 : Nat.totient 125320289714899177316204329650 = 30276998970169356462435840000 := by
  rw [← show ((([(2, 1), (3, 3), (5, 2), (19, 1), (23, 1), (10949, 1), (11731, 1), (30253, 1), (54667378301, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_19, prime_oneHundredSixCZ_23, prime_oneHundredSixCZ_10949, prime_oneHundredSixCZ_11731, prime_oneHundredSixCZ_30253, prime_oneHundredSixCZ_54667378301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329651 : Nat.totient 125320289714899177316204329651 = 125315814150108102026846200000 := by
  rw [← show ((([(28001, 1), (4475564791075289358101651, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_28001, prime_oneHundredSixCZ_4475564791075289358101651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329652 : Nat.totient 125320289714899177316204329652 = 62660136339818580118826446848 := by
  rw [← show ((([(2, 2), (7461073, 1), (525020833, 1), (7998040021757, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_7461073, prime_oneHundredSixCZ_525020833, prime_oneHundredSixCZ_7998040021757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329653 : Nat.totient 125320289714899177316204329653 = 74355932039547144302774016000 := by
  rw [← show ((([(3, 1), (11, 1), (53, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_11, prime_oneHundredSixCZ_53, prime_oneHundredSixCZ_461, prime_oneHundredSixCZ_69997, prime_oneHundredSixCZ_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329654 : Nat.totient 125320289714899177316204329654 = 62656565127424365396861741312 := by
  rw [← show ((([(2, 1), (19997, 1), (140407, 1), (22317101458347153313, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_19997, prime_oneHundredSixCZ_140407, prime_oneHundredSixCZ_22317101458347153313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329655 : Nat.totient 125320289714899177316204329655 = 85118693446951444720387584000 := by
  rw [← show ((([(5, 1), (7, 1), (109, 1), (5861, 1), (6917, 1), (810284163285790201, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_109, prime_oneHundredSixCZ_5861, prime_oneHundredSixCZ_6917, prime_oneHundredSixCZ_810284163285790201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329656 : Nat.totient 125320289714899177316204329656 = 41773429904966392438734776544 := by
  rw [← show ((([(2, 3), (3, 1), (5221678738120799054841847069, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_5221678738120799054841847069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329657 : Nat.totient 125320289714899177316204329657 = 122653699301099568176177824752 := by
  rw [← show ((([(47, 1), (609397, 1), (4375454987258216338523, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_47, prime_oneHundredSixCZ_609397, prime_oneHundredSixCZ_4375454987258216338523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329658 : Nat.totient 125320289714899177316204329658 = 62074499773153077790378604496 := by
  rw [← show ((([(2, 1), (107, 1), (1712219, 1), (342017481667622015413, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_107, prime_oneHundredSixCZ_1712219, prime_oneHundredSixCZ_342017481667622015413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329659 : Nat.totient 125320289714899177316204329659 = 78427112965855109743677014016 := by
  rw [← show ((([(3, 2), (17, 1), (467, 1), (2749, 1), (9473, 1), (3080939, 1), (21860883103, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_17, prime_oneHundredSixCZ_467, prime_oneHundredSixCZ_2749, prime_oneHundredSixCZ_9473, prime_oneHundredSixCZ_3080939, prime_oneHundredSixCZ_21860883103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329660 : Nat.totient 125320289714899177316204329660 = 45021509485934673264532445952 := by
  rw [← show ((([(2, 2), (5, 1), (13, 1), (37, 1), (13027057142920912402931843, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_13, prime_oneHundredSixCZ_37, prime_oneHundredSixCZ_13027057142920912402931843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329661 : Nat.totient 125320289714899177316204329661 = 119192946676857272094876787248 := by
  rw [← show ((([(29, 1), (67, 1), (64498347768862160224500427, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_29, prime_oneHundredSixCZ_67, prime_oneHundredSixCZ_64498347768862160224500427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329662 : Nat.totient 125320289714899177316204329662 = 35805797061399764947486951320 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (2983816421783313745623912611, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_2983816421783313745623912611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329663 : Nat.totient 125320289714899177316204329663 = 125320289714895725715598596648 := by
  rw [← show ((([(36698057394307, 1), (3414902548338709, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_36698057394307, prime_oneHundredSixCZ_3414902548338709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329664 : Nat.totient 125320289714899177316204329664 = 56692375990236367832526566400 := by
  rw [← show ((([(2, 6), (11, 1), (211, 1), (39883, 1), (610806899, 1), (34631756843, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_11, prime_oneHundredSixCZ_211, prime_oneHundredSixCZ_39883, prime_oneHundredSixCZ_610806899, prime_oneHundredSixCZ_34631756843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329665 : Nat.totient 125320289714899177316204329665 = 66831570723136620282958392576 := by
  rw [← show ((([(3, 1), (5, 1), (12109, 1), (168143, 1), (4103392498243839653, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_12109, prime_oneHundredSixCZ_168143, prime_oneHundredSixCZ_4103392498243839653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329666 : Nat.totient 125320289714899177316204329666 = 62458665291237716500773851280 := by
  rw [← show ((([(2, 1), (311, 1), (82857392227, 1), (2431642609582189, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_311, prime_oneHundredSixCZ_82857392227, prime_oneHundredSixCZ_2431642609582189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329667 : Nat.totient 125320289714899177316204329667 = 122263681625096534327197195840 := by
  rw [← show ((([(41, 1), (7808519, 1), (391443298283670903773, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_41, prime_oneHundredSixCZ_7808519, prime_oneHundredSixCZ_391443298283670903773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329668 : Nat.totient 125320289714899177316204329668 = 41773311888592068098637246000 := by
  rw [← show ((([(2, 2), (3, 2), (353963, 1), (9834697860361674440251, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_353963, prime_oneHundredSixCZ_9834697860361674440251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329669 : Nat.totient 125320289714899177316204329669 = 101748617530660370478336156000 := by
  rw [← show ((([(7, 2), (19, 1), (8803, 1), (27751, 1), (551013665718067483, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_19, prime_oneHundredSixCZ_8803, prime_oneHundredSixCZ_27751, prime_oneHundredSixCZ_551013665718067483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329670 : Nat.totient 125320289714899177316204329670 = 49424847745408394587401959424 := by
  rw [← show ((([(2, 1), (5, 1), (127, 1), (337, 1), (463, 1), (919, 1), (1095487, 1), (628179902447, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_127, prime_oneHundredSixCZ_337, prime_oneHundredSixCZ_463, prime_oneHundredSixCZ_919, prime_oneHundredSixCZ_1095487, prime_oneHundredSixCZ_628179902447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329671 : Nat.totient 125320289714899177316204329671 = 82677149780603159086893299712 := by
  rw [← show ((([(3, 1), (137, 1), (349, 1), (3719, 1), (3623952329, 1), (64825442039, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_137, prime_oneHundredSixCZ_349, prime_oneHundredSixCZ_3719, prime_oneHundredSixCZ_3623952329, prime_oneHundredSixCZ_64825442039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329672 : Nat.totient 125320289714899177316204329672 = 62660144849746881399992416464 := by
  rw [← show ((([(2, 3), (8134821047, 1), (1925676806392616047, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_8134821047, prime_oneHundredSixCZ_1925676806392616047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329673 : Nat.totient 125320289714899177316204329673 = 110647999466592541056596032320 := by
  rw [← show ((([(13, 1), (23, 1), (41117, 1), (10193628030468171081431, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_13, prime_oneHundredSixCZ_23, prime_oneHundredSixCZ_41117, prime_oneHundredSixCZ_10193628030468171081431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329674 : Nat.totient 125320289714899177316204329674 = 41496733948564790060532393600 := by
  rw [← show ((([(2, 1), (3, 1), (151, 1), (916259, 1), (7633859, 1), (19775651719609, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_151, prime_oneHundredSixCZ_916259, prime_oneHundredSixCZ_7633859, prime_oneHundredSixCZ_19775651719609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329675 : Nat.totient 125320289714899177316204329675 = 90986761372688143605136308000 := by
  rw [← show ((([(5, 2), (11, 1), (587, 1), (776337554374472215060891, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_11, prime_oneHundredSixCZ_587, prime_oneHundredSixCZ_776337554374472215060891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329676 : Nat.totient 125320289714899177316204329676 = 48918735996415792790249963520 := by
  rw [← show ((([(2, 2), (7, 1), (17, 1), (31, 1), (1828808833, 1), (4643916828201787, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_17, prime_oneHundredSixCZ_31, prime_oneHundredSixCZ_1828808833, prime_oneHundredSixCZ_4643916828201787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329677 : Nat.totient 125320289714899177316204329677 = 83546859809747062046395855296 := by
  rw [← show ((([(3, 3), (449866622033, 1), (10317485193027847, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_449866622033, prime_oneHundredSixCZ_10317485193027847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329678 : Nat.totient 125320289714899177316204329678 = 62655904920947789081926269792 := by
  rw [← show ((([(2, 1), (14797, 1), (21048647, 1), (27249407, 1), (7383061403, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_14797, prime_oneHundredSixCZ_21048647, prime_oneHundredSixCZ_27249407, prime_oneHundredSixCZ_7383061403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329679 : Nat.totient 125320289714899177316204329679 = 122082655293910262325092929056 := by
  rw [← show ((([(43, 1), (379, 1), (511963, 1), (15020180420292872789, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_43, prime_oneHundredSixCZ_379, prime_oneHundredSixCZ_511963, prime_oneHundredSixCZ_15020180420292872789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329680 : Nat.totient 125320289714899177316204329680 = 32286626193846296116747026432 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (59, 1), (89, 1), (167, 1), (15667, 1), (38007194700201613, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_59, prime_oneHundredSixCZ_89, prime_oneHundredSixCZ_167, prime_oneHundredSixCZ_15667, prime_oneHundredSixCZ_38007194700201613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329681 : Nat.totient 125320289714899177316204329681 = 125320289026800192831815814000 := by
  rw [← show ((([(182125381, 1), (688098984484206390301, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_182125381, prime_oneHundredSixCZ_688098984484206390301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329682 : Nat.totient 125320289714899177316204329682 = 62482336789896650226038545920 := by
  rw [← show ((([(2, 1), (353, 1), (207877, 1), (853906360559472657461, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_353, prime_oneHundredSixCZ_207877, prime_oneHundredSixCZ_853906360559472657461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329683 : Nat.totient 125320289714899177316204329683 = 71611594122791628763178190336 := by
  rw [← show ((([(3, 1), (7, 1), (9191779315207, 1), (649235870327489, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_9191779315207, prime_oneHundredSixCZ_649235870327489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329684 : Nat.totient 125320289714899177316204329684 = 62410233299771893743622800000 := by
  rw [← show ((([(2, 2), (251, 1), (231551, 1), (4683745333, 1), (115092690637, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_251, prime_oneHundredSixCZ_231551, prime_oneHundredSixCZ_4683745333, prime_oneHundredSixCZ_115092690637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329685 : Nat.totient 125320289714899177316204329685 = 100230787645017063278787802368 := by
  rw [← show ((([(5, 1), (4909, 1), (19963, 1), (971707547, 1), (263206718813, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_4909, prime_oneHundredSixCZ_19963, prime_oneHundredSixCZ_971707547, prime_oneHundredSixCZ_263206718813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329686 : Nat.totient 125320289714899177316204329686 = 35042821513188538396522032000 := by
  rw [← show ((([(2, 1), (3, 2), (11, 2), (13, 2), (3371, 1), (24923, 1), (4052450700197531, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_11, prime_oneHundredSixCZ_13, prime_oneHundredSixCZ_3371, prime_oneHundredSixCZ_24923, prime_oneHundredSixCZ_4052450700197531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329687 : Nat.totient 125320289714899177316204329687 = 125318019479446126086353769600 := by
  rw [← show ((([(57731, 1), (1259821, 1), (1723072164228297137, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_57731, prime_oneHundredSixCZ_1259821, prime_oneHundredSixCZ_1723072164228297137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329688 : Nat.totient 125320289714899177316204329688 = 59361405464385867017324552832 := by
  rw [← show ((([(2, 3), (19, 1), (73243, 1), (2235949, 1), (5034423944422567, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_19, prime_oneHundredSixCZ_73243, prime_oneHundredSixCZ_2235949, prime_oneHundredSixCZ_5034423944422567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329689 : Nat.totient 125320289714899177316204329689 = 82413834050458499894970275520 := by
  rw [← show ((([(3, 1), (79, 1), (1093, 1), (2945622871, 1), (164238790852399, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_79, prime_oneHundredSixCZ_1093, prime_oneHundredSixCZ_2945622871, prime_oneHundredSixCZ_164238790852399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329690 : Nat.totient 125320289714899177316204329690 = 41485337260889341193216478720 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (29, 1), (1725478681, 1), (35777974856637683, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_29, prime_oneHundredSixCZ_1725478681, prime_oneHundredSixCZ_35777974856637683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329691 : Nat.totient 125320289714899177316204329691 = 125320289714896397972322709392 := by
  rw [← show ((([(45846128675203, 1), (2733497752945097, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_45846128675203, prime_oneHundredSixCZ_2733497752945097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329692 : Nat.totient 125320289714899177316204329692 = 41770682411177616553593504000 := by
  rw [← show ((([(2, 2), (3, 1), (27541, 1), (33941, 1), (11172125489077444261, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_27541, prime_oneHundredSixCZ_33941, prime_oneHundredSixCZ_11172125489077444261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329693 : Nat.totient 125320289714899177316204329693 = 117800517361019065646990192640 := by
  rw [← show ((([(17, 1), (797, 1), (18887317177, 1), (489715526829241, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_17, prime_oneHundredSixCZ_797, prime_oneHundredSixCZ_18887317177, prime_oneHundredSixCZ_489715526829241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329694 : Nat.totient 125320289714899177316204329694 = 62628609807194203862602363080 := by
  rw [← show ((([(2, 1), (1987, 1), (31535050255384795499799781, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_1987, prime_oneHundredSixCZ_31535050255384795499799781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329695 : Nat.totient 125320289714899177316204329695 = 66825241979567857260079917312 := by
  rw [← show ((([(3, 2), (5, 1), (5479, 1), (1430789, 1), (248970947, 1), (1426866403, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_5479, prime_oneHundredSixCZ_1430789, prime_oneHundredSixCZ_248970947, prime_oneHundredSixCZ_1426866403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329696 : Nat.totient 125320289714899177316204329696 = 59933367418256972511812481024 := by
  rw [← show ((([(2, 5), (23, 1), (24733, 1), (28551438473, 1), (241123081229, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_23, prime_oneHundredSixCZ_24733, prime_oneHundredSixCZ_28551438473, prime_oneHundredSixCZ_241123081229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329697 : Nat.totient 125320289714899177316204329697 = 94976812738638965425294080000 := by
  rw [← show ((([(7, 1), (11, 1), (37, 1), (2633, 1), (4502371, 1), (15287581, 1), (242715791, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_7, prime_oneHundredSixCZ_11, prime_oneHundredSixCZ_37, prime_oneHundredSixCZ_2633, prime_oneHundredSixCZ_4502371, prime_oneHundredSixCZ_15287581, prime_oneHundredSixCZ_242715791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329698 : Nat.totient 125320289714899177316204329698 = 41773379238959181144065250048 := by
  rw [← show ((([(2, 1), (3, 1), (936917, 1), (6870673, 1), (3244664082498463, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_936917, prime_oneHundredSixCZ_6870673, prime_oneHundredSixCZ_3244664082498463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329699 : Nat.totient 125320289714899177316204329699 = 115673439503795639613127741728 := by
  rw [← show ((([(13, 1), (16943, 1), (371773307, 1), (1530416088182323, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_13, prime_oneHundredSixCZ_16943, prime_oneHundredSixCZ_371773307, prime_oneHundredSixCZ_1530416088182323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329700 : Nat.totient 125320289714899177316204329700 = 49926798541399609722603110400 := by
  rw [← show ((([(2, 2), (5, 2), (347, 1), (881, 1), (423389, 1), (18058783, 1), (536152033, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_2, prime_oneHundredSixCZ_5, prime_oneHundredSixCZ_347, prime_oneHundredSixCZ_881, prime_oneHundredSixCZ_423389, prime_oneHundredSixCZ_18058783, prime_oneHundredSixCZ_536152033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixCZ_125320289714899177316204329701 : Nat.totient 125320289714899177316204329701 = 82402380392090849255550208896 := by
  rw [← show ((([(3, 1), (73, 1), (43687003, 1), (13098604310793702893, 1)] : List FactorBlock).map factorBlockValue).prod) = 125320289714899177316204329701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixCZ_3, prime_oneHundredSixCZ_73, prime_oneHundredSixCZ_43687003, prime_oneHundredSixCZ_13098604310793702893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixCZ : certifiedKill 1 125320289714899177316204329599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixCZ_125320289714899177316204329600, phi_oneHundredSixCZ_125320289714899177316204329601, phi_oneHundredSixCZ_125320289714899177316204329602,
    phi_oneHundredSixCZ_125320289714899177316204329603, phi_oneHundredSixCZ_125320289714899177316204329604, phi_oneHundredSixCZ_125320289714899177316204329605,
    phi_oneHundredSixCZ_125320289714899177316204329606, phi_oneHundredSixCZ_125320289714899177316204329607, phi_oneHundredSixCZ_125320289714899177316204329608,
    phi_oneHundredSixCZ_125320289714899177316204329609, phi_oneHundredSixCZ_125320289714899177316204329610, phi_oneHundredSixCZ_125320289714899177316204329611,
    phi_oneHundredSixCZ_125320289714899177316204329612, phi_oneHundredSixCZ_125320289714899177316204329613, phi_oneHundredSixCZ_125320289714899177316204329614,
    phi_oneHundredSixCZ_125320289714899177316204329615, phi_oneHundredSixCZ_125320289714899177316204329616, phi_oneHundredSixCZ_125320289714899177316204329617,
    phi_oneHundredSixCZ_125320289714899177316204329618, phi_oneHundredSixCZ_125320289714899177316204329619, phi_oneHundredSixCZ_125320289714899177316204329620,
    phi_oneHundredSixCZ_125320289714899177316204329621, phi_oneHundredSixCZ_125320289714899177316204329622, phi_oneHundredSixCZ_125320289714899177316204329623,
    phi_oneHundredSixCZ_125320289714899177316204329624, phi_oneHundredSixCZ_125320289714899177316204329625, phi_oneHundredSixCZ_125320289714899177316204329626,
    phi_oneHundredSixCZ_125320289714899177316204329627, phi_oneHundredSixCZ_125320289714899177316204329628, phi_oneHundredSixCZ_125320289714899177316204329629,
    phi_oneHundredSixCZ_125320289714899177316204329630, phi_oneHundredSixCZ_125320289714899177316204329631, phi_oneHundredSixCZ_125320289714899177316204329632,
    phi_oneHundredSixCZ_125320289714899177316204329633, phi_oneHundredSixCZ_125320289714899177316204329634, phi_oneHundredSixCZ_125320289714899177316204329635,
    phi_oneHundredSixCZ_125320289714899177316204329636, phi_oneHundredSixCZ_125320289714899177316204329637, phi_oneHundredSixCZ_125320289714899177316204329638,
    phi_oneHundredSixCZ_125320289714899177316204329639, phi_oneHundredSixCZ_125320289714899177316204329640, phi_oneHundredSixCZ_125320289714899177316204329641,
    phi_oneHundredSixCZ_125320289714899177316204329642, phi_oneHundredSixCZ_125320289714899177316204329643, phi_oneHundredSixCZ_125320289714899177316204329644,
    phi_oneHundredSixCZ_125320289714899177316204329645, phi_oneHundredSixCZ_125320289714899177316204329646, phi_oneHundredSixCZ_125320289714899177316204329647,
    phi_oneHundredSixCZ_125320289714899177316204329648, phi_oneHundredSixCZ_125320289714899177316204329649, phi_oneHundredSixCZ_125320289714899177316204329650,
    phi_oneHundredSixCZ_125320289714899177316204329651, phi_oneHundredSixCZ_125320289714899177316204329652, phi_oneHundredSixCZ_125320289714899177316204329653,
    phi_oneHundredSixCZ_125320289714899177316204329654, phi_oneHundredSixCZ_125320289714899177316204329655, phi_oneHundredSixCZ_125320289714899177316204329656,
    phi_oneHundredSixCZ_125320289714899177316204329657, phi_oneHundredSixCZ_125320289714899177316204329658, phi_oneHundredSixCZ_125320289714899177316204329659,
    phi_oneHundredSixCZ_125320289714899177316204329660, phi_oneHundredSixCZ_125320289714899177316204329661, phi_oneHundredSixCZ_125320289714899177316204329662,
    phi_oneHundredSixCZ_125320289714899177316204329663, phi_oneHundredSixCZ_125320289714899177316204329664, phi_oneHundredSixCZ_125320289714899177316204329665,
    phi_oneHundredSixCZ_125320289714899177316204329666, phi_oneHundredSixCZ_125320289714899177316204329667, phi_oneHundredSixCZ_125320289714899177316204329668,
    phi_oneHundredSixCZ_125320289714899177316204329669, phi_oneHundredSixCZ_125320289714899177316204329670, phi_oneHundredSixCZ_125320289714899177316204329671,
    phi_oneHundredSixCZ_125320289714899177316204329672, phi_oneHundredSixCZ_125320289714899177316204329673, phi_oneHundredSixCZ_125320289714899177316204329674,
    phi_oneHundredSixCZ_125320289714899177316204329675, phi_oneHundredSixCZ_125320289714899177316204329676, phi_oneHundredSixCZ_125320289714899177316204329677,
    phi_oneHundredSixCZ_125320289714899177316204329678, phi_oneHundredSixCZ_125320289714899177316204329679, phi_oneHundredSixCZ_125320289714899177316204329680,
    phi_oneHundredSixCZ_125320289714899177316204329681, phi_oneHundredSixCZ_125320289714899177316204329682, phi_oneHundredSixCZ_125320289714899177316204329683,
    phi_oneHundredSixCZ_125320289714899177316204329684, phi_oneHundredSixCZ_125320289714899177316204329685, phi_oneHundredSixCZ_125320289714899177316204329686,
    phi_oneHundredSixCZ_125320289714899177316204329687, phi_oneHundredSixCZ_125320289714899177316204329688, phi_oneHundredSixCZ_125320289714899177316204329689,
    phi_oneHundredSixCZ_125320289714899177316204329690, phi_oneHundredSixCZ_125320289714899177316204329691, phi_oneHundredSixCZ_125320289714899177316204329692,
    phi_oneHundredSixCZ_125320289714899177316204329693, phi_oneHundredSixCZ_125320289714899177316204329694, phi_oneHundredSixCZ_125320289714899177316204329695,
    phi_oneHundredSixCZ_125320289714899177316204329696, phi_oneHundredSixCZ_125320289714899177316204329697, phi_oneHundredSixCZ_125320289714899177316204329698,
    phi_oneHundredSixCZ_125320289714899177316204329699, phi_oneHundredSixCZ_125320289714899177316204329700, phi_oneHundredSixCZ_125320289714899177316204329701
    ]

end TotientTailPeriodKiller
end Erdos249257
