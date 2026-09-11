import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFiftyOneESFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFiftyOneESFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFiftyOneESFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFiftyOneESFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFiftyOneESFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFiftyOneESFastPow a n * oneHundredFiftyOneESFastPow a n * a else oneHundredFiftyOneESFastPow a n * oneHundredFiftyOneESFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFiftyOneES_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFiftyOneES_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFiftyOneES_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFiftyOneES_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFiftyOneES_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFiftyOneES_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFiftyOneES_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFiftyOneES_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFiftyOneES_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFiftyOneES_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFiftyOneES_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFiftyOneES_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFiftyOneES_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFiftyOneES_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFiftyOneES_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFiftyOneES_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFiftyOneES_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFiftyOneES_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFiftyOneES_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFiftyOneES_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFiftyOneES_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFiftyOneES_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFiftyOneES_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFiftyOneES_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFiftyOneES_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFiftyOneES_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFiftyOneES_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFiftyOneES_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFiftyOneES_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFiftyOneES_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFiftyOneES_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFiftyOneES_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFiftyOneES_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFiftyOneES_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFiftyOneES_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFiftyOneES_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFiftyOneES_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFiftyOneES_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFiftyOneES_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFiftyOneES_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFiftyOneES_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFiftyOneES_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFiftyOneES_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFiftyOneES_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFiftyOneES_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFiftyOneES_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFiftyOneES_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFiftyOneES_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFiftyOneES_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFiftyOneES_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFiftyOneES_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFiftyOneES_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFiftyOneES_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFiftyOneES_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFiftyOneES_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFiftyOneES_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFiftyOneES_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFiftyOneES_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFiftyOneES_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFiftyOneES_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFiftyOneES_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFiftyOneES_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredFiftyOneES_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredFiftyOneES_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredFiftyOneES_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFiftyOneES_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredFiftyOneES_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFiftyOneES_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFiftyOneES_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredFiftyOneES_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredFiftyOneES_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredFiftyOneES_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFiftyOneES_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredFiftyOneES_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredFiftyOneES_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFiftyOneES_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredFiftyOneES_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredFiftyOneES_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredFiftyOneES_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredFiftyOneES_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredFiftyOneES_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFiftyOneES_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredFiftyOneES_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredFiftyOneES_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredFiftyOneES_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredFiftyOneES_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredFiftyOneES_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredFiftyOneES_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredFiftyOneES_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredFiftyOneES_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredFiftyOneES_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredFiftyOneES_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredFiftyOneES_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredFiftyOneES_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredFiftyOneES_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredFiftyOneES_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredFiftyOneES_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredFiftyOneES_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredFiftyOneES_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredFiftyOneES_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredFiftyOneES_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredFiftyOneES_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredFiftyOneES_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredFiftyOneES_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredFiftyOneES_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredFiftyOneES_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredFiftyOneES_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredFiftyOneES_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredFiftyOneES_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredFiftyOneES_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredFiftyOneES_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredFiftyOneES_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredFiftyOneES_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredFiftyOneES_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredFiftyOneES_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredFiftyOneES_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredFiftyOneES_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_oneHundredFiftyOneES_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredFiftyOneES_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_oneHundredFiftyOneES_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredFiftyOneES_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_oneHundredFiftyOneES_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_oneHundredFiftyOneES_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_oneHundredFiftyOneES_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredFiftyOneES_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_oneHundredFiftyOneES_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredFiftyOneES_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_oneHundredFiftyOneES_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredFiftyOneES_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredFiftyOneES_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_oneHundredFiftyOneES_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredFiftyOneES_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredFiftyOneES_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_oneHundredFiftyOneES_2089 : Nat.Prime 2089 := by norm_num

private theorem prime_oneHundredFiftyOneES_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_oneHundredFiftyOneES_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_oneHundredFiftyOneES_2179 : Nat.Prime 2179 := by norm_num

private theorem prime_oneHundredFiftyOneES_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_oneHundredFiftyOneES_2221 : Nat.Prime 2221 := by norm_num

private theorem prime_oneHundredFiftyOneES_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_oneHundredFiftyOneES_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_oneHundredFiftyOneES_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_oneHundredFiftyOneES_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_oneHundredFiftyOneES_2351 : Nat.Prime 2351 := by norm_num

private theorem prime_oneHundredFiftyOneES_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_oneHundredFiftyOneES_2459 : Nat.Prime 2459 := by norm_num

private theorem prime_oneHundredFiftyOneES_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_oneHundredFiftyOneES_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_oneHundredFiftyOneES_2671 : Nat.Prime 2671 := by norm_num

private theorem prime_oneHundredFiftyOneES_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_oneHundredFiftyOneES_2719 : Nat.Prime 2719 := by norm_num

private theorem prime_oneHundredFiftyOneES_2753 : Nat.Prime 2753 := by norm_num

private theorem prime_oneHundredFiftyOneES_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredFiftyOneES_2953 : Nat.Prime 2953 := by norm_num

private theorem prime_oneHundredFiftyOneES_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_oneHundredFiftyOneES_3181 : Nat.Prime 3181 := by norm_num

private theorem prime_oneHundredFiftyOneES_3187 : Nat.Prime 3187 := by norm_num

private theorem prime_oneHundredFiftyOneES_3191 : Nat.Prime 3191 := by norm_num

private theorem prime_oneHundredFiftyOneES_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_oneHundredFiftyOneES_3407 : Nat.Prime 3407 := by norm_num

private theorem prime_oneHundredFiftyOneES_3559 : Nat.Prime 3559 := by norm_num

private theorem prime_oneHundredFiftyOneES_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_oneHundredFiftyOneES_3793 : Nat.Prime 3793 := by norm_num

private theorem prime_oneHundredFiftyOneES_3823 : Nat.Prime 3823 := by norm_num

private theorem prime_oneHundredFiftyOneES_3877 : Nat.Prime 3877 := by norm_num

private theorem prime_oneHundredFiftyOneES_4007 : Nat.Prime 4007 := by norm_num

private theorem prime_oneHundredFiftyOneES_4027 : Nat.Prime 4027 := by norm_num

private theorem prime_oneHundredFiftyOneES_4157 : Nat.Prime 4157 := by norm_num

private theorem prime_oneHundredFiftyOneES_4283 : Nat.Prime 4283 := by norm_num

private theorem prime_oneHundredFiftyOneES_4337 : Nat.Prime 4337 := by norm_num

private theorem prime_oneHundredFiftyOneES_4357 : Nat.Prime 4357 := by norm_num

private theorem prime_oneHundredFiftyOneES_4513 : Nat.Prime 4513 := by norm_num

private theorem prime_oneHundredFiftyOneES_4649 : Nat.Prime 4649 := by norm_num

private theorem prime_oneHundredFiftyOneES_4651 : Nat.Prime 4651 := by norm_num

private theorem prime_oneHundredFiftyOneES_4663 : Nat.Prime 4663 := by norm_num

private theorem prime_oneHundredFiftyOneES_4691 : Nat.Prime 4691 := by norm_num

private theorem prime_oneHundredFiftyOneES_4793 : Nat.Prime 4793 := by norm_num

private theorem prime_oneHundredFiftyOneES_5023 : Nat.Prime 5023 := by norm_num

private theorem prime_oneHundredFiftyOneES_5171 : Nat.Prime 5171 := by norm_num

private theorem prime_oneHundredFiftyOneES_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_oneHundredFiftyOneES_5981 : Nat.Prime 5981 := by norm_num

private theorem prime_oneHundredFiftyOneES_5987 : Nat.Prime 5987 := by norm_num

private theorem prime_oneHundredFiftyOneES_6029 : Nat.Prime 6029 := by norm_num

private theorem prime_oneHundredFiftyOneES_6037 : Nat.Prime 6037 := by norm_num

private theorem prime_oneHundredFiftyOneES_6199 : Nat.Prime 6199 := by norm_num

private theorem prime_oneHundredFiftyOneES_6247 : Nat.Prime 6247 := by norm_num

private theorem prime_oneHundredFiftyOneES_6257 : Nat.Prime 6257 := by norm_num

private theorem prime_oneHundredFiftyOneES_6263 : Nat.Prime 6263 := by norm_num

private theorem prime_oneHundredFiftyOneES_6379 : Nat.Prime 6379 := by norm_num

private theorem prime_oneHundredFiftyOneES_6553 : Nat.Prime 6553 := by norm_num

private theorem prime_oneHundredFiftyOneES_6857 : Nat.Prime 6857 := by norm_num

private theorem prime_oneHundredFiftyOneES_7001 : Nat.Prime 7001 := by norm_num

private theorem prime_oneHundredFiftyOneES_7243 : Nat.Prime 7243 := by norm_num

private theorem prime_oneHundredFiftyOneES_7321 : Nat.Prime 7321 := by norm_num

private theorem prime_oneHundredFiftyOneES_7523 : Nat.Prime 7523 := by norm_num

private theorem prime_oneHundredFiftyOneES_7603 : Nat.Prime 7603 := by norm_num

private theorem prime_oneHundredFiftyOneES_8039 : Nat.Prime 8039 := by norm_num

private theorem prime_oneHundredFiftyOneES_8513 : Nat.Prime 8513 := by norm_num

private theorem prime_oneHundredFiftyOneES_8647 : Nat.Prime 8647 := by norm_num

private theorem prime_oneHundredFiftyOneES_8719 : Nat.Prime 8719 := by norm_num

private theorem prime_oneHundredFiftyOneES_8831 : Nat.Prime 8831 := by norm_num

private theorem prime_oneHundredFiftyOneES_8867 : Nat.Prime 8867 := by norm_num

private theorem prime_oneHundredFiftyOneES_8893 : Nat.Prime 8893 := by norm_num

private theorem prime_oneHundredFiftyOneES_9059 : Nat.Prime 9059 := by norm_num

private theorem prime_oneHundredFiftyOneES_9187 : Nat.Prime 9187 := by norm_num

private theorem prime_oneHundredFiftyOneES_9887 : Nat.Prime 9887 := by norm_num

private theorem prime_oneHundredFiftyOneES_10079 : Nat.Prime 10079 := by norm_num

private theorem prime_oneHundredFiftyOneES_10133 : Nat.Prime 10133 := by norm_num

private theorem prime_oneHundredFiftyOneES_10313 : Nat.Prime 10313 := by norm_num

private theorem prime_oneHundredFiftyOneES_10343 : Nat.Prime 10343 := by norm_num

private theorem prime_oneHundredFiftyOneES_10487 : Nat.Prime 10487 := by norm_num

private theorem prime_oneHundredFiftyOneES_10531 : Nat.Prime 10531 := by norm_num

private theorem prime_oneHundredFiftyOneES_10993 : Nat.Prime 10993 := by norm_num

private theorem prime_oneHundredFiftyOneES_11093 : Nat.Prime 11093 := by norm_num

private theorem prime_oneHundredFiftyOneES_11113 : Nat.Prime 11113 := by norm_num

private theorem prime_oneHundredFiftyOneES_11587 : Nat.Prime 11587 := by norm_num

private theorem prime_oneHundredFiftyOneES_11689 : Nat.Prime 11689 := by norm_num

private theorem prime_oneHundredFiftyOneES_11863 : Nat.Prime 11863 := by norm_num

private theorem prime_oneHundredFiftyOneES_12227 : Nat.Prime 12227 := by norm_num

private theorem prime_oneHundredFiftyOneES_12347 : Nat.Prime 12347 := by norm_num

private theorem prime_oneHundredFiftyOneES_12641 : Nat.Prime 12641 := by norm_num

private theorem prime_oneHundredFiftyOneES_14321 : Nat.Prime 14321 := by norm_num

private theorem prime_oneHundredFiftyOneES_14387 : Nat.Prime 14387 := by norm_num

private theorem prime_oneHundredFiftyOneES_14621 : Nat.Prime 14621 := by norm_num

private theorem prime_oneHundredFiftyOneES_15161 : Nat.Prime 15161 := by norm_num

private theorem prime_oneHundredFiftyOneES_15401 : Nat.Prime 15401 := by norm_num

private theorem prime_oneHundredFiftyOneES_15647 : Nat.Prime 15647 := by norm_num

private theorem prime_oneHundredFiftyOneES_15727 : Nat.Prime 15727 := by norm_num

private theorem prime_oneHundredFiftyOneES_15937 : Nat.Prime 15937 := by norm_num

private theorem prime_oneHundredFiftyOneES_15991 : Nat.Prime 15991 := by norm_num

private theorem prime_oneHundredFiftyOneES_16339 : Nat.Prime 16339 := by norm_num

private theorem prime_oneHundredFiftyOneES_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFiftyOneES_17291 : Nat.Prime 17291 := by norm_num

private theorem prime_oneHundredFiftyOneES_17293 : Nat.Prime 17293 := by norm_num

private theorem prime_oneHundredFiftyOneES_17471 : Nat.Prime 17471 := by norm_num

private theorem prime_oneHundredFiftyOneES_17657 : Nat.Prime 17657 := by norm_num

private theorem prime_oneHundredFiftyOneES_18077 : Nat.Prime 18077 := by norm_num

private theorem prime_oneHundredFiftyOneES_18481 : Nat.Prime 18481 := by norm_num

private theorem prime_oneHundredFiftyOneES_19231 : Nat.Prime 19231 := by norm_num

private theorem prime_oneHundredFiftyOneES_19373 : Nat.Prime 19373 := by norm_num

private theorem prime_oneHundredFiftyOneES_19777 : Nat.Prime 19777 := by norm_num

private theorem prime_oneHundredFiftyOneES_19813 : Nat.Prime 19813 := by norm_num

private theorem prime_oneHundredFiftyOneES_20147 : Nat.Prime 20147 := by norm_num

private theorem prime_oneHundredFiftyOneES_20149 : Nat.Prime 20149 := by norm_num

private theorem prime_oneHundredFiftyOneES_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFiftyOneES_20947 : Nat.Prime 20947 := by norm_num

private theorem prime_oneHundredFiftyOneES_24979 : Nat.Prime 24979 := by norm_num

private theorem prime_oneHundredFiftyOneES_26459 : Nat.Prime 26459 := by norm_num

private theorem prime_oneHundredFiftyOneES_27701 : Nat.Prime 27701 := by norm_num

private theorem prime_oneHundredFiftyOneES_29429 : Nat.Prime 29429 := by norm_num

private theorem prime_oneHundredFiftyOneES_30497 : Nat.Prime 30497 := by norm_num

private theorem prime_oneHundredFiftyOneES_30557 : Nat.Prime 30557 := by norm_num

private theorem prime_oneHundredFiftyOneES_31741 : Nat.Prime 31741 := by norm_num

private theorem prime_oneHundredFiftyOneES_32561 : Nat.Prime 32561 := by norm_num

private theorem prime_oneHundredFiftyOneES_32611 : Nat.Prime 32611 := by norm_num

private theorem prime_oneHundredFiftyOneES_32653 : Nat.Prime 32653 := by norm_num

private theorem prime_oneHundredFiftyOneES_33317 : Nat.Prime 33317 := by norm_num

private theorem prime_oneHundredFiftyOneES_34961 : Nat.Prime 34961 := by norm_num

private theorem prime_oneHundredFiftyOneES_35159 : Nat.Prime 35159 := by norm_num

private theorem prime_oneHundredFiftyOneES_37897 : Nat.Prime 37897 := by norm_num

private theorem prime_oneHundredFiftyOneES_38153 : Nat.Prime 38153 := by norm_num

private theorem prime_oneHundredFiftyOneES_41381 : Nat.Prime 41381 := by norm_num

private theorem prime_oneHundredFiftyOneES_43891 : Nat.Prime 43891 := by norm_num

private theorem prime_oneHundredFiftyOneES_47309 : Nat.Prime 47309 := by norm_num

private theorem prime_oneHundredFiftyOneES_51061 : Nat.Prime 51061 := by norm_num

private theorem prime_oneHundredFiftyOneES_52639 : Nat.Prime 52639 := by norm_num

private theorem prime_oneHundredFiftyOneES_55579 : Nat.Prime 55579 := by norm_num

private theorem prime_oneHundredFiftyOneES_63527 : Nat.Prime 63527 := by norm_num

private theorem prime_oneHundredFiftyOneES_63997 : Nat.Prime 63997 := by norm_num

private theorem prime_oneHundredFiftyOneES_64187 : Nat.Prime 64187 := by norm_num

private theorem prime_oneHundredFiftyOneES_64609 : Nat.Prime 64609 := by norm_num

private theorem prime_oneHundredFiftyOneES_68483 : Nat.Prime 68483 := by norm_num

private theorem prime_oneHundredFiftyOneES_71353 : Nat.Prime 71353 := by norm_num

private theorem prime_oneHundredFiftyOneES_72973 : Nat.Prime 72973 := by norm_num

private theorem prime_oneHundredFiftyOneES_79979 : Nat.Prime 79979 := by norm_num

private theorem prime_oneHundredFiftyOneES_83701 : Nat.Prime 83701 := by norm_num

private theorem prime_oneHundredFiftyOneES_83833 : Nat.Prime 83833 := by norm_num

private theorem prime_oneHundredFiftyOneES_89381 : Nat.Prime 89381 := by norm_num

private theorem prime_oneHundredFiftyOneES_90901 : Nat.Prime 90901 := by norm_num

private theorem prime_oneHundredFiftyOneES_94907 : Nat.Prime 94907 := by norm_num

private theorem prime_oneHundredFiftyOneES_99929 : Nat.Prime 99929 := by norm_num

private theorem prime_oneHundredFiftyOneES_100183 : Nat.Prime 100183 := by norm_num

private theorem prime_oneHundredFiftyOneES_100693 : Nat.Prime 100693 := by norm_num

private theorem prime_oneHundredFiftyOneES_101789 : Nat.Prime 101789 := by norm_num

private theorem prime_oneHundredFiftyOneES_105167 : Nat.Prime 105167 := by norm_num

private theorem prime_oneHundredFiftyOneES_108187 : Nat.Prime 108187 := by norm_num

private theorem prime_oneHundredFiftyOneES_118621 : Nat.Prime 118621 := by norm_num

private theorem prime_oneHundredFiftyOneES_118927 : Nat.Prime 118927 := by norm_num

private theorem prime_oneHundredFiftyOneES_119101 : Nat.Prime 119101 := by norm_num

private theorem prime_oneHundredFiftyOneES_121333 : Nat.Prime 121333 := by norm_num

private theorem prime_oneHundredFiftyOneES_123307 : Nat.Prime 123307 := by norm_num

private theorem prime_oneHundredFiftyOneES_127373 : Nat.Prime 127373 := by norm_num

private theorem prime_oneHundredFiftyOneES_128111 : Nat.Prime 128111 := by norm_num

private theorem prime_oneHundredFiftyOneES_135613 : Nat.Prime 135613 := by norm_num

private theorem prime_oneHundredFiftyOneES_147089 : Nat.Prime 147089 := by norm_num

private theorem prime_oneHundredFiftyOneES_160507 : Nat.Prime 160507 := by norm_num

private theorem prime_oneHundredFiftyOneES_163811 : Nat.Prime 163811 := by norm_num

private theorem prime_oneHundredFiftyOneES_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFiftyOneES_180629 : Nat.Prime 180629 := by norm_num

private theorem prime_oneHundredFiftyOneES_182839 : Nat.Prime 182839 := by norm_num

private theorem prime_oneHundredFiftyOneES_184007 : Nat.Prime 184007 := by norm_num

private theorem prime_oneHundredFiftyOneES_184351 : Nat.Prime 184351 := by norm_num

private theorem prime_oneHundredFiftyOneES_198479 : Nat.Prime 198479 := by norm_num

private theorem prime_oneHundredFiftyOneES_200779 : Nat.Prime 200779 := by norm_num

private theorem prime_oneHundredFiftyOneES_202393 : Nat.Prime 202393 := by norm_num

private theorem prime_oneHundredFiftyOneES_229351 : Nat.Prime 229351 := by norm_num

private theorem prime_oneHundredFiftyOneES_233201 : Nat.Prime 233201 := by norm_num

private theorem prime_oneHundredFiftyOneES_237173 : Nat.Prime 237173 := by norm_num

private theorem prime_oneHundredFiftyOneES_240007 : Nat.Prime 240007 := by norm_num

private theorem prime_oneHundredFiftyOneES_249433 : Nat.Prime 249433 := by norm_num

private theorem prime_oneHundredFiftyOneES_290201 : Nat.Prime 290201 := by norm_num

private theorem prime_oneHundredFiftyOneES_295039 : Nat.Prime 295039 := by norm_num

private theorem prime_oneHundredFiftyOneES_295073 : Nat.Prime 295073 := by norm_num

private theorem prime_oneHundredFiftyOneES_299567 : Nat.Prime 299567 := by norm_num

private theorem prime_oneHundredFiftyOneES_307859 : Nat.Prime 307859 := by norm_num

private theorem prime_oneHundredFiftyOneES_322079 : Nat.Prime 322079 := by norm_num

private theorem prime_oneHundredFiftyOneES_335029 : Nat.Prime 335029 := by norm_num

private theorem prime_oneHundredFiftyOneES_338563 : Nat.Prime 338563 := by norm_num

private theorem prime_oneHundredFiftyOneES_339091 : Nat.Prime 339091 := by norm_num

private theorem prime_oneHundredFiftyOneES_340979 : Nat.Prime 340979 := by norm_num

private theorem prime_oneHundredFiftyOneES_361409 : Nat.Prime 361409 := by norm_num

private theorem prime_oneHundredFiftyOneES_380707 : Nat.Prime 380707 := by norm_num

private theorem prime_oneHundredFiftyOneES_387641 : Nat.Prime 387641 := by norm_num

private theorem prime_oneHundredFiftyOneES_389149 : Nat.Prime 389149 := by norm_num

private theorem prime_oneHundredFiftyOneES_395047 : Nat.Prime 395047 := by norm_num

private theorem prime_oneHundredFiftyOneES_411311 : Nat.Prime 411311 := by norm_num

private theorem prime_oneHundredFiftyOneES_414083 : Nat.Prime 414083 := by norm_num

private theorem prime_oneHundredFiftyOneES_415189 : Nat.Prime 415189 := by norm_num

private theorem prime_oneHundredFiftyOneES_416513 : Nat.Prime 416513 := by norm_num

private theorem prime_oneHundredFiftyOneES_438601 : Nat.Prime 438601 := by norm_num

private theorem prime_oneHundredFiftyOneES_474941 : Nat.Prime 474941 := by norm_num

private theorem prime_oneHundredFiftyOneES_485059 : Nat.Prime 485059 := by norm_num

private theorem prime_oneHundredFiftyOneES_487247 : Nat.Prime 487247 := by norm_num

private theorem prime_oneHundredFiftyOneES_496019 : Nat.Prime 496019 := by norm_num

private theorem prime_oneHundredFiftyOneES_503453 : Nat.Prime 503453 := by norm_num

private theorem prime_oneHundredFiftyOneES_513881 : Nat.Prime 513881 := by norm_num

private theorem prime_oneHundredFiftyOneES_532739 : Nat.Prime 532739 := by norm_num

private theorem prime_oneHundredFiftyOneES_598229 : Nat.Prime 598229 := by norm_num

private theorem prime_oneHundredFiftyOneES_601283 : Nat.Prime 601283 := by norm_num

private theorem prime_oneHundredFiftyOneES_670493 : Nat.Prime 670493 := by norm_num

private theorem prime_oneHundredFiftyOneES_677639 : Nat.Prime 677639 := by norm_num

private theorem prime_oneHundredFiftyOneES_731909 : Nat.Prime 731909 := by norm_num

private theorem prime_oneHundredFiftyOneES_741857 : Nat.Prime 741857 := by norm_num

private theorem prime_oneHundredFiftyOneES_749893 : Nat.Prime 749893 := by norm_num

private theorem prime_oneHundredFiftyOneES_763043 : Nat.Prime 763043 := by norm_num

private theorem prime_oneHundredFiftyOneES_795127 : Nat.Prime 795127 := by norm_num

private theorem prime_oneHundredFiftyOneES_837721 : Nat.Prime 837721 := by norm_num

private theorem prime_oneHundredFiftyOneES_857333 : Nat.Prime 857333 := by norm_num

private theorem prime_oneHundredFiftyOneES_904781 : Nat.Prime 904781 := by norm_num

private theorem prime_oneHundredFiftyOneES_954599 : Nat.Prime 954599 := by norm_num

private theorem prime_oneHundredFiftyOneES_1047773 : Nat.Prime 1047773 := by norm_num

private theorem prime_oneHundredFiftyOneES_1064059 : Nat.Prime 1064059 := by norm_num

private theorem prime_oneHundredFiftyOneES_1091191 : Nat.Prime 1091191 := by norm_num

private theorem prime_oneHundredFiftyOneES_1119389 : Nat.Prime 1119389 := by norm_num

private theorem prime_oneHundredFiftyOneES_1160207 : Nat.Prime 1160207 := by norm_num

private theorem prime_oneHundredFiftyOneES_1216421 : Nat.Prime 1216421 := by norm_num

private theorem prime_oneHundredFiftyOneES_1326503 : Nat.Prime 1326503 := by norm_num

private theorem prime_oneHundredFiftyOneES_1368487 : Nat.Prime 1368487 := by norm_num

private theorem prime_oneHundredFiftyOneES_1452203 : Nat.Prime 1452203 := by norm_num

private theorem prime_oneHundredFiftyOneES_1578701 : Nat.Prime 1578701 := by norm_num

private theorem prime_oneHundredFiftyOneES_1604297 : Nat.Prime 1604297 := by norm_num

private theorem prime_oneHundredFiftyOneES_1927591 : Nat.Prime 1927591 := by norm_num

private theorem prime_oneHundredFiftyOneES_1960201 : Nat.Prime 1960201 := by norm_num

private theorem prime_oneHundredFiftyOneES_1976453 : Nat.Prime 1976453 := by norm_num

private theorem prime_oneHundredFiftyOneES_1983731 : Nat.Prime 1983731 := by norm_num

private theorem prime_oneHundredFiftyOneES_2014081 : Nat.Prime 2014081 := by norm_num

private theorem prime_oneHundredFiftyOneES_2017283 : Nat.Prime 2017283 := by norm_num

private theorem prime_oneHundredFiftyOneES_2027569 : Nat.Prime 2027569 := by norm_num

private theorem prime_oneHundredFiftyOneES_2091361 : Nat.Prime 2091361 := by norm_num

private theorem prime_oneHundredFiftyOneES_2189339 : Nat.Prime 2189339 := by norm_num

private theorem prime_oneHundredFiftyOneES_2604191 : Nat.Prime 2604191 := by norm_num

private theorem prime_oneHundredFiftyOneES_2632151 : Nat.Prime 2632151 := by norm_num

private theorem prime_oneHundredFiftyOneES_2739761 : Nat.Prime 2739761 := by norm_num

private theorem prime_oneHundredFiftyOneES_2901739 : Nat.Prime 2901739 := by norm_num

private theorem prime_oneHundredFiftyOneES_3254071 : Nat.Prime 3254071 := by norm_num

private theorem prime_oneHundredFiftyOneES_3343243 : Nat.Prime 3343243 := by norm_num

private theorem prime_oneHundredFiftyOneES_3549047 : Nat.Prime 3549047 := by norm_num

private theorem prime_oneHundredFiftyOneES_3718783 : Nat.Prime 3718783 := by norm_num

private theorem prime_oneHundredFiftyOneES_3813353 : Nat.Prime 3813353 := by norm_num

private theorem prime_oneHundredFiftyOneES_4022873 : Nat.Prime 4022873 := by norm_num

private theorem prime_oneHundredFiftyOneES_4099861 : Nat.Prime 4099861 := by norm_num

private theorem prime_oneHundredFiftyOneES_4161257 : Nat.Prime 4161257 := by norm_num

private theorem prime_oneHundredFiftyOneES_4324157 : Nat.Prime 4324157 := by norm_num

private theorem prime_oneHundredFiftyOneES_4391851 : Nat.Prime 4391851 := by norm_num

private theorem prime_oneHundredFiftyOneES_4403543 : Nat.Prime 4403543 := by norm_num

private theorem prime_oneHundredFiftyOneES_4481173 : Nat.Prime 4481173 := by norm_num

private theorem prime_oneHundredFiftyOneES_4790339 : Nat.Prime 4790339 := by norm_num

private theorem prime_oneHundredFiftyOneES_4981747 : Nat.Prime 4981747 := by norm_num

private theorem prime_oneHundredFiftyOneES_5082551 : Nat.Prime 5082551 := by norm_num

private theorem prime_oneHundredFiftyOneES_5259167 : Nat.Prime 5259167 := by norm_num

private theorem prime_oneHundredFiftyOneES_5475791 : Nat.Prime 5475791 := by norm_num

private theorem prime_oneHundredFiftyOneES_5506481 : Nat.Prime 5506481 := by norm_num

private theorem prime_oneHundredFiftyOneES_6085987 : Nat.Prime 6085987 := by norm_num

private theorem prime_oneHundredFiftyOneES_6452863 : Nat.Prime 6452863 := by norm_num

private theorem prime_oneHundredFiftyOneES_6743381 : Nat.Prime 6743381 := by norm_num

private theorem prime_oneHundredFiftyOneES_6768889 : Nat.Prime 6768889 := by norm_num

private theorem prime_oneHundredFiftyOneES_7100897 : Nat.Prime 7100897 := by norm_num

private theorem prime_oneHundredFiftyOneES_7752137 : Nat.Prime 7752137 := by norm_num

private theorem prime_oneHundredFiftyOneES_8050379 : Nat.Prime 8050379 := by norm_num

private theorem prime_oneHundredFiftyOneES_8316857 : Nat.Prime 8316857 := by norm_num

private theorem prime_oneHundredFiftyOneES_9946247 : Nat.Prime 9946247 := by norm_num

private theorem prime_oneHundredFiftyOneES_10044193 : Nat.Prime 10044193 := by norm_num

private theorem prime_oneHundredFiftyOneES_10541737 : Nat.Prime 10541737 := by norm_num

private theorem prime_oneHundredFiftyOneES_10799177 : Nat.Prime 10799177 := by norm_num

private theorem prime_oneHundredFiftyOneES_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFiftyOneES_10874887 : Nat.Prime 10874887 := by norm_num

private theorem prime_oneHundredFiftyOneES_11372429 : Nat.Prime 11372429 := by norm_num

private theorem prime_oneHundredFiftyOneES_13077299 : Nat.Prime 13077299 := by norm_num

private theorem prime_oneHundredFiftyOneES_13787539 : Nat.Prime 13787539 := by norm_num

private theorem prime_oneHundredFiftyOneES_14102981 : Nat.Prime 14102981 := by norm_num

private theorem prime_oneHundredFiftyOneES_15283547 : Nat.Prime 15283547 := by norm_num

private theorem prime_oneHundredFiftyOneES_15579929 : Nat.Prime 15579929 := by norm_num

private theorem prime_oneHundredFiftyOneES_15789517 : Nat.Prime 15789517 := by norm_num

private theorem prime_oneHundredFiftyOneES_16656173 : Nat.Prime 16656173 := by norm_num

private theorem prime_oneHundredFiftyOneES_17625319 : Nat.Prime 17625319 := by norm_num

private theorem prime_oneHundredFiftyOneES_17629721 : Nat.Prime 17629721 := by norm_num

private theorem prime_oneHundredFiftyOneES_18642179 : Nat.Prime 18642179 := by norm_num

private theorem prime_oneHundredFiftyOneES_18845921 : Nat.Prime 18845921 := by norm_num

private theorem prime_oneHundredFiftyOneES_18969767 : Nat.Prime 18969767 := by norm_num

private theorem prime_oneHundredFiftyOneES_19909837 : Nat.Prime 19909837 := by norm_num

private theorem prime_oneHundredFiftyOneES_20292367 : Nat.Prime 20292367 := by norm_num

private theorem prime_oneHundredFiftyOneES_20479159 : Nat.Prime 20479159 := by norm_num

private theorem prime_oneHundredFiftyOneES_21193043 : Nat.Prime 21193043 := by norm_num

private theorem prime_oneHundredFiftyOneES_22286161 : Nat.Prime 22286161 := by norm_num

private theorem prime_oneHundredFiftyOneES_22355779 : Nat.Prime 22355779 := by norm_num

private theorem prime_oneHundredFiftyOneES_22847743 : Nat.Prime 22847743 := by norm_num

private theorem prime_oneHundredFiftyOneES_25848413 : Nat.Prime 25848413 := by norm_num

private theorem prime_oneHundredFiftyOneES_27891887 : Nat.Prime 27891887 := by norm_num

private theorem prime_oneHundredFiftyOneES_32692861 : Nat.Prime 32692861 := by
  apply lucas_primality 32692861 (7 : ZMod 32692861)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (29, 1), (6263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (29, 1), (6263, 1)] : List FactorBlock).map factorBlockValue).prod) = 32692861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_6263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32692861) ^ 16346430 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 32692861) ^ 10897620 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 32692861) ^ 6538572 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 32692861) ^ 1127340 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 32692861) ^ 5220 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_38717179 : Nat.Prime 38717179 := by
  apply lucas_primality 38717179 (2 : ZMod 38717179)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6452863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6452863, 1)] : List FactorBlock).map factorBlockValue).prod) = 38717179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_6452863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38717179) ^ 19358589 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 38717179) ^ 12905726 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 38717179) ^ 6 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_44659711 : Nat.Prime 44659711 := by
  apply lucas_primality 44659711 (3 : ZMod 44659711)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (29, 1), (71, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (29, 1), (71, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) = 44659711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_71
      · exact prime_oneHundredFiftyOneES_241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44659711) ^ 22329855 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 44659711) ^ 14886570 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 44659711) ^ 8931942 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 44659711) ^ 1539990 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 44659711) ^ 629010 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 44659711) ^ 185310 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_49634561 : Nat.Prime 49634561 := by
  apply lucas_primality 49634561 (13 : ZMod 49634561)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (17, 1), (2281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (17, 1), (2281, 1)] : List FactorBlock).map factorBlockValue).prod) = 49634561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_2281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 49634561) ^ 24817280 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 49634561) ^ 9926912 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 49634561) ^ 2919680 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 49634561) ^ 21760 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_55779827 : Nat.Prime 55779827 := by
  apply lucas_primality 55779827 (2 : ZMod 55779827)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2351, 1), (11863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2351, 1), (11863, 1)] : List FactorBlock).map factorBlockValue).prod) = 55779827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_2351
      · exact prime_oneHundredFiftyOneES_11863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55779827) ^ 27889913 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 55779827) ^ 23726 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 55779827) ^ 4702 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_57971621 : Nat.Prime 57971621 := by
  apply lucas_primality 57971621 (2 : ZMod 57971621)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (414083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (414083, 1)] : List FactorBlock).map factorBlockValue).prod) = 57971621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_414083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57971621) ^ 28985810 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 57971621) ^ 11594324 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 57971621) ^ 8281660 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 57971621) ^ 140 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_60447007 : Nat.Prime 60447007 := by
  apply lucas_primality 60447007 (3 : ZMod 60447007)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1119389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1119389, 1)] : List FactorBlock).map factorBlockValue).prod) = 60447007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_1119389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 60447007) ^ 30223503 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 60447007) ^ 20149002 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 60447007) ^ 54 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_66567367 : Nat.Prime 66567367 := by
  apply lucas_primality 66567367 (3 : ZMod 66567367)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (33317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (33317, 1)] : List FactorBlock).map factorBlockValue).prod) = 66567367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_37
      · exact prime_oneHundredFiftyOneES_33317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66567367) ^ 33283683 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 66567367) ^ 22189122 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 66567367) ^ 1799118 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 66567367) ^ 1998 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_66767131 : Nat.Prime 66767131 := by
  apply lucas_primality 66767131 (2 : ZMod 66767131)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (741857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (741857, 1)] : List FactorBlock).map factorBlockValue).prod) = 66767131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_741857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66767131) ^ 33383565 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 66767131) ^ 22255710 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 66767131) ^ 13353426 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 66767131) ^ 90 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_67335629 : Nat.Prime 67335629 := by
  apply lucas_primality 67335629 (3 : ZMod 67335629)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (731909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (731909, 1)] : List FactorBlock).map factorBlockValue).prod) = 67335629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_731909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 67335629) ^ 33667814 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 67335629) ^ 2927636 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 67335629) ^ 92 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_68794993 : Nat.Prime 68794993 := by
  apply lucas_primality 68794993 (5 : ZMod 68794993)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (139, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (139, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 68794993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_139
      · exact prime_oneHundredFiftyOneES_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 68794993) ^ 34397496 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 68794993) ^ 22931664 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 68794993) ^ 9827856 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 68794993) ^ 494928 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 68794993) ^ 140112 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_70589069 : Nat.Prime 70589069 := by
  apply lucas_primality 70589069 (2 : ZMod 70589069)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1604297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1604297, 1)] : List FactorBlock).map factorBlockValue).prod) = 70589069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_1604297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 70589069) ^ 35294534 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 70589069) ^ 6417188 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 70589069) ^ 44 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_71698769 : Nat.Prime 71698769 := by
  apply lucas_primality 71698769 (3 : ZMod 71698769)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4481173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4481173, 1)] : List FactorBlock).map factorBlockValue).prod) = 71698769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_4481173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 71698769) ^ 35849384 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 71698769) ^ 16 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_81153949 : Nat.Prime 81153949 := by
  apply lucas_primality 81153949 (2 : ZMod 81153949)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (233201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (233201, 1)] : List FactorBlock).map factorBlockValue).prod) = 81153949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_233201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 81153949) ^ 40576974 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 81153949) ^ 27051316 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 81153949) ^ 2798412 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 81153949) ^ 348 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_85123463 : Nat.Prime 85123463 := by
  apply lucas_primality 85123463 (5 : ZMod 85123463)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (71, 1), (14621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (71, 1), (14621, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_41
      · exact prime_oneHundredFiftyOneES_71
      · exact prime_oneHundredFiftyOneES_14621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 85123463) ^ 42561731 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 85123463) ^ 2076182 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 85123463) ^ 1198922 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 85123463) ^ 5822 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_93505567 : Nat.Prime 93505567 := by
  apply lucas_primality 93505567 (3 : ZMod 93505567)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (202393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (202393, 1)] : List FactorBlock).map factorBlockValue).prod) = 93505567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_202393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93505567) ^ 46752783 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 93505567) ^ 31168522 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 93505567) ^ 13357938 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 93505567) ^ 8500506 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 93505567) ^ 462 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_99937039 : Nat.Prime 99937039 := by
  apply lucas_primality 99937039 (3 : ZMod 99937039)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (16656173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (16656173, 1)] : List FactorBlock).map factorBlockValue).prod) = 99937039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_16656173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 99937039) ^ 49968519 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 99937039) ^ 33312346 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 99937039) ^ 6 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_108933283 : Nat.Prime 108933283 := by
  apply lucas_primality 108933283 (2 : ZMod 108933283)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2017283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2017283, 1)] : List FactorBlock).map factorBlockValue).prod) = 108933283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_2017283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 108933283) ^ 54466641 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 108933283) ^ 36311094 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 108933283) ^ 54 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_110332289 : Nat.Prime 110332289 := by
  apply lucas_primality 110332289 (6 : ZMod 110332289)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (11, 1), (23, 1), (3407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (11, 1), (23, 1), (3407, 1)] : List FactorBlock).map factorBlockValue).prod) = 110332289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_3407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 110332289) ^ 55166144 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 110332289) ^ 10030208 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 110332289) ^ 4797056 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 110332289) ^ 32384 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_113631509 : Nat.Prime 113631509 := by
  apply lucas_primality 113631509 (2 : ZMod 113631509)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (389149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (389149, 1)] : List FactorBlock).map factorBlockValue).prod) = 113631509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_73
      · exact prime_oneHundredFiftyOneES_389149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 113631509) ^ 56815754 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 113631509) ^ 1556596 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 113631509) ^ 292 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_114607849 : Nat.Prime 114607849 := by
  apply lucas_primality 114607849 (7 : ZMod 114607849)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (127, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (127, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod) = 114607849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_127
      · exact prime_oneHundredFiftyOneES_1979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 114607849) ^ 57303924 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 114607849) ^ 38202616 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 114607849) ^ 6031992 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 114607849) ^ 902424 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 114607849) ^ 57912 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_114815381 : Nat.Prime 114815381 := by
  apply lucas_primality 114815381 (2 : ZMod 114815381)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (359, 1), (15991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (359, 1), (15991, 1)] : List FactorBlock).map factorBlockValue).prod) = 114815381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_359
      · exact prime_oneHundredFiftyOneES_15991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 114815381) ^ 57407690 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 114815381) ^ 22963076 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 114815381) ^ 319820 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 114815381) ^ 7180 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_116138689 : Nat.Prime 116138689 := by
  apply lucas_primality 116138689 (17 : ZMod 116138689)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (53, 1), (101, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (53, 1), (101, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 116138689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_53
      · exact prime_oneHundredFiftyOneES_101
      · exact prime_oneHundredFiftyOneES_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 116138689) ^ 58069344 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 116138689) ^ 38712896 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 116138689) ^ 2191296 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 116138689) ^ 1149888 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 116138689) ^ 1027776 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_119393429 : Nat.Prime 119393429 := by
  apply lucas_primality 119393429 (2 : ZMod 119393429)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (387641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (387641, 1)] : List FactorBlock).map factorBlockValue).prod) = 119393429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_387641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 119393429) ^ 59696714 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 119393429) ^ 17056204 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 119393429) ^ 10853948 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 119393429) ^ 308 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_120699013 : Nat.Prime 120699013 := by
  apply lucas_primality 120699013 (2 : ZMod 120699013)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (191, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (191, 1), (7523, 1)] : List FactorBlock).map factorBlockValue).prod) = 120699013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_191
      · exact prime_oneHundredFiftyOneES_7523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 120699013) ^ 60349506 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 120699013) ^ 40233004 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 120699013) ^ 17242716 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 120699013) ^ 631932 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 120699013) ^ 16044 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_120844861 : Nat.Prime 120844861 := by
  apply lucas_primality 120844861 (2 : ZMod 120844861)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2014081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2014081, 1)] : List FactorBlock).map factorBlockValue).prod) = 120844861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_2014081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 120844861) ^ 60422430 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 120844861) ^ 40281620 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 120844861) ^ 24168972 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 120844861) ^ 60 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_137582383 : Nat.Prime 137582383 := by
  apply lucas_primality 137582383 (3 : ZMod 137582383)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (53, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (53, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 137582383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_53
      · exact prime_oneHundredFiftyOneES_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 137582383) ^ 68791191 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 137582383) ^ 45860794 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 137582383) ^ 19654626 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 137582383) ^ 7241178 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 137582383) ^ 2595894 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 137582383) ^ 42294 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_141037769 : Nat.Prime 141037769 := by
  apply lucas_primality 141037769 (3 : ZMod 141037769)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17629721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17629721, 1)] : List FactorBlock).map factorBlockValue).prod) = 141037769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_17629721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 141037769) ^ 70518884 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 141037769) ^ 8 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_174372071 : Nat.Prime 174372071 := by
  apply lucas_primality 174372071 (11 : ZMod 174372071)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (601283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (601283, 1)] : List FactorBlock).map factorBlockValue).prod) = 174372071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_601283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 174372071) ^ 87186035 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 174372071) ^ 34874414 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 174372071) ^ 6012830 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 174372071) ^ 290 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_174557839 : Nat.Prime 174557839 := by
  apply lucas_primality 174557839 (3 : ZMod 174557839)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (31, 1), (10313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (31, 1), (10313, 1)] : List FactorBlock).map factorBlockValue).prod) = 174557839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_10313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 174557839) ^ 87278919 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 174557839) ^ 58185946 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 174557839) ^ 24936834 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 174557839) ^ 13427526 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 174557839) ^ 5630898 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 174557839) ^ 16926 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_174695441 : Nat.Prime 174695441 := by
  apply lucas_primality 174695441 (6 : ZMod 174695441)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (349, 1), (6257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (349, 1), (6257, 1)] : List FactorBlock).map factorBlockValue).prod) = 174695441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_349
      · exact prime_oneHundredFiftyOneES_6257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 174695441) ^ 87347720 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 174695441) ^ 34939088 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 174695441) ^ 500560 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 174695441) ^ 27920 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_175830409 : Nat.Prime 175830409 := by
  apply lucas_primality 175830409 (7 : ZMod 175830409)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (19, 1), (9887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (19, 1), (9887, 1)] : List FactorBlock).map factorBlockValue).prod) = 175830409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_9887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 175830409) ^ 87915204 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 175830409) ^ 58610136 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 175830409) ^ 13525416 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 175830409) ^ 9254232 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 175830409) ^ 17784 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_185401393 : Nat.Prime 185401393 := by
  apply lucas_primality 185401393 (10 : ZMod 185401393)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (19, 1), (18481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (19, 1), (18481, 1)] : List FactorBlock).map factorBlockValue).prod) = 185401393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_18481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 185401393) ^ 92700696 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 185401393) ^ 61800464 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 185401393) ^ 16854672 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 185401393) ^ 9757968 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 185401393) ^ 10032 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_220664579 : Nat.Prime 220664579 := by
  apply lucas_primality 220664579 (2 : ZMod 220664579)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (110332289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (110332289, 1)] : List FactorBlock).map factorBlockValue).prod) = 220664579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_110332289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 220664579) ^ 110332289 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 220664579) ^ 2 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_233005361 : Nat.Prime 233005361 := by
  apply lucas_primality 233005361 (3 : ZMod 233005361)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (19, 1), (61, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (19, 1), (61, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) = 233005361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_61
      · exact prime_oneHundredFiftyOneES_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 233005361) ^ 116502680 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 233005361) ^ 46601072 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 233005361) ^ 33286480 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 233005361) ^ 12263440 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 233005361) ^ 3819760 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 233005361) ^ 649040 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_292866391 : Nat.Prime 292866391 := by
  apply lucas_primality 292866391 (6 : ZMod 292866391)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (3254071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (3254071, 1)] : List FactorBlock).map factorBlockValue).prod) = 292866391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_3254071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 292866391) ^ 146433195 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 292866391) ^ 97622130 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 292866391) ^ 58573278 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 292866391) ^ 90 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_345760769 : Nat.Prime 345760769 := by
  apply lucas_primality 345760769 (3 : ZMod 345760769)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (59, 2), (97, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (59, 2), (97, 1)] : List FactorBlock).map factorBlockValue).prod) = 345760769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_59
      · exact prime_oneHundredFiftyOneES_97
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 345760769) ^ 172880384 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 345760769) ^ 5860352 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 345760769) ^ 3564544 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_366805129 : Nat.Prime 366805129 := by
  apply lucas_primality 366805129 (14 : ZMod 366805129)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (15283547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (15283547, 1)] : List FactorBlock).map factorBlockValue).prod) = 366805129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_15283547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 366805129) ^ 183402564 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (14 : ZMod 366805129) ^ 122268376 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (14 : ZMod 366805129) ^ 24 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_377041391 : Nat.Prime 377041391 := by
  apply lucas_primality 377041391 (11 : ZMod 377041391)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (173, 1), (19813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (173, 1), (19813, 1)] : List FactorBlock).map factorBlockValue).prod) = 377041391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_173
      · exact prime_oneHundredFiftyOneES_19813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 377041391) ^ 188520695 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 377041391) ^ 75408278 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 377041391) ^ 34276490 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 377041391) ^ 2179430 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 377041391) ^ 19030 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_394108079 : Nat.Prime 394108079 := by
  apply lucas_primality 394108079 (7 : ZMod 394108079)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13, 1), (71, 1), (4357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13, 1), (71, 1), (4357, 1)] : List FactorBlock).map factorBlockValue).prod) = 394108079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_71
      · exact prime_oneHundredFiftyOneES_4357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 394108079) ^ 197054039 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 394108079) ^ 56301154 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 394108079) ^ 30316006 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 394108079) ^ 5550818 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 394108079) ^ 90454 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_442516031 : Nat.Prime 442516031 := by
  apply lucas_primality 442516031 (11 : ZMod 442516031)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (4022873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (4022873, 1)] : List FactorBlock).map factorBlockValue).prod) = 442516031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_4022873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 442516031) ^ 221258015 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 442516031) ^ 88503206 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 442516031) ^ 40228730 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 442516031) ^ 110 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_460136431 : Nat.Prime 460136431 := by
  apply lucas_primality 460136431 (3 : ZMod 460136431)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (13, 1), (337, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (13, 1), (337, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) = 460136431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_337
      · exact prime_oneHundredFiftyOneES_389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 460136431) ^ 230068215 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 460136431) ^ 153378810 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 460136431) ^ 92027286 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 460136431) ^ 35395110 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 460136431) ^ 1365390 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 460136431) ^ 1182870 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_464423677 : Nat.Prime 464423677 := by
  apply lucas_primality 464423677 (2 : ZMod 464423677)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (433, 1), (89381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (433, 1), (89381, 1)] : List FactorBlock).map factorBlockValue).prod) = 464423677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_433
      · exact prime_oneHundredFiftyOneES_89381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 464423677) ^ 232211838 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 464423677) ^ 154807892 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 464423677) ^ 1072572 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 464423677) ^ 5196 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_485957551 : Nat.Prime 485957551 := by
  apply lucas_primality 485957551 (6 : ZMod 485957551)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 1), (31, 1), (8039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 1), (31, 1), (8039, 1)] : List FactorBlock).map factorBlockValue).prod) = 485957551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_8039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 485957551) ^ 242978775 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 485957551) ^ 161985850 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 485957551) ^ 97191510 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 485957551) ^ 37381350 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 485957551) ^ 15676050 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 485957551) ^ 60450 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_500878909 : Nat.Prime 500878909 := by
  apply lucas_primality 500878909 (2 : ZMod 500878909)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (557, 1), (24979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (557, 1), (24979, 1)] : List FactorBlock).map factorBlockValue).prod) = 500878909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_557
      · exact prime_oneHundredFiftyOneES_24979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 500878909) ^ 250439454 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 500878909) ^ 166959636 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 500878909) ^ 899244 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 500878909) ^ 20052 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_545391601 : Nat.Prime 545391601 := by
  apply lucas_primality 545391601 (7 : ZMod 545391601)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (13, 1), (34961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (13, 1), (34961, 1)] : List FactorBlock).map factorBlockValue).prod) = 545391601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_34961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 545391601) ^ 272695800 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 545391601) ^ 181797200 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 545391601) ^ 109078320 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 545391601) ^ 41953200 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 545391601) ^ 15600 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_616935581 : Nat.Prime 616935581 := by
  apply lucas_primality 616935581 (2 : ZMod 616935581)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1747, 1), (17657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1747, 1), (17657, 1)] : List FactorBlock).map factorBlockValue).prod) = 616935581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_1747
      · exact prime_oneHundredFiftyOneES_17657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 616935581) ^ 308467790 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 616935581) ^ 123387116 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 616935581) ^ 353140 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 616935581) ^ 34940 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_17203
      · exact prime_oneHundredFiftyOneES_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_766421083 : Nat.Prime 766421083 := by
  apply lucas_primality 766421083 (2 : ZMod 766421083)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (2027569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (2027569, 1)] : List FactorBlock).map factorBlockValue).prod) = 766421083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_2027569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 766421083) ^ 383210541 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 766421083) ^ 255473694 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 766421083) ^ 109488726 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 766421083) ^ 378 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_881393531 : Nat.Prime 881393531 := by
  apply lucas_primality 881393531 (2 : ZMod 881393531)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (479, 1), (184007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (479, 1), (184007, 1)] : List FactorBlock).map factorBlockValue).prod) = 881393531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_479
      · exact prime_oneHundredFiftyOneES_184007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 881393531) ^ 440696765 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 881393531) ^ 176278706 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 881393531) ^ 1840070 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 881393531) ^ 4790 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_961482373 : Nat.Prime 961482373 := by
  apply lucas_primality 961482373 (5 : ZMod 961482373)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6553, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6553, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) = 961482373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_6553
      · exact prime_oneHundredFiftyOneES_12227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 961482373) ^ 480741186 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 961482373) ^ 320494124 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 961482373) ^ 146724 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 961482373) ^ 78636 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_962978057 : Nat.Prime 962978057 := by
  apply lucas_primality 962978057 (3 : ZMod 962978057)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 2), (416513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 2), (416513, 1)] : List FactorBlock).map factorBlockValue).prod) = 962978057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_416513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 962978057) ^ 481489028 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 962978057) ^ 56645768 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 962978057) ^ 2312 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1043178431 : Nat.Prime 1043178431 := by
  apply lucas_primality 1043178431 (14 : ZMod 1043178431)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (29, 1), (513881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (29, 1), (513881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1043178431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_513881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1043178431) ^ 521589215 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (14 : ZMod 1043178431) ^ 208635686 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (14 : ZMod 1043178431) ^ 149025490 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (14 : ZMod 1043178431) ^ 35971670 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (14 : ZMod 1043178431) ^ 2030 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1140925213 : Nat.Prime 1140925213 := by
  apply lucas_primality 1140925213 (2 : ZMod 1140925213)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (23, 1), (61, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (23, 1), (61, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) = 1140925213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_61
      · exact prime_oneHundredFiftyOneES_461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1140925213) ^ 570462606 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1140925213) ^ 380308404 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1140925213) ^ 162989316 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1140925213) ^ 49605444 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1140925213) ^ 18703692 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1140925213) ^ 2474892 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1164248909 : Nat.Prime 1164248909 := by
  apply lucas_primality 1164248909 (2 : ZMod 1164248909)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (6768889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (6768889, 1)] : List FactorBlock).map factorBlockValue).prod) = 1164248909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_43
      · exact prime_oneHundredFiftyOneES_6768889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1164248909) ^ 582124454 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164248909) ^ 27075556 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164248909) ^ 172 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1348286561 : Nat.Prime 1348286561 := by
  apply lucas_primality 1348286561 (3 : ZMod 1348286561)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (29, 1), (67, 1), (4337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (29, 1), (67, 1), (4337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348286561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_67
      · exact prime_oneHundredFiftyOneES_4337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1348286561) ^ 674143280 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1348286561) ^ 269657312 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1348286561) ^ 46492640 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1348286561) ^ 20123680 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1348286561) ^ 310880 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1359408839 : Nat.Prime 1359408839 := by
  apply lucas_primality 1359408839 (17 : ZMod 1359408839)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1973, 1), (11113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1973, 1), (11113, 1)] : List FactorBlock).map factorBlockValue).prod) = 1359408839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_1973
      · exact prime_oneHundredFiftyOneES_11113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1359408839) ^ 679704419 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 1359408839) ^ 43851898 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 1359408839) ^ 689006 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 1359408839) ^ 122326 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1685936969 : Nat.Prime 1685936969 := by
  apply lucas_primality 1685936969 (3 : ZMod 1685936969)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (89, 1), (63997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (89, 1), (63997, 1)] : List FactorBlock).map factorBlockValue).prod) = 1685936969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_37
      · exact prime_oneHundredFiftyOneES_89
      · exact prime_oneHundredFiftyOneES_63997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1685936969) ^ 842968484 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1685936969) ^ 45565864 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1685936969) ^ 18943112 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1685936969) ^ 26344 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1749592157 : Nat.Prime 1749592157 := by
  apply lucas_primality 1749592157 (2 : ZMod 1749592157)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (29, 1), (1160207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (29, 1), (1160207, 1)] : List FactorBlock).map factorBlockValue).prod) = 1749592157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_1160207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1749592157) ^ 874796078 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1749592157) ^ 134584012 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1749592157) ^ 60330764 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1749592157) ^ 1508 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2090977661 : Nat.Prime 2090977661 := by
  apply lucas_primality 2090977661 (2 : ZMod 2090977661)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (349, 1), (299567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (349, 1), (299567, 1)] : List FactorBlock).map factorBlockValue).prod) = 2090977661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_349
      · exact prime_oneHundredFiftyOneES_299567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2090977661) ^ 1045488830 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2090977661) ^ 418195532 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2090977661) ^ 5991340 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2090977661) ^ 6980 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2600125301 : Nat.Prime 2600125301 := by
  apply lucas_primality 2600125301 (2 : ZMod 2600125301)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (19, 1), (1368487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (19, 1), (1368487, 1)] : List FactorBlock).map factorBlockValue).prod) = 2600125301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_1368487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2600125301) ^ 1300062650 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2600125301) ^ 520025060 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2600125301) ^ 136848700 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2600125301) ^ 1900 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_3142041103 : Nat.Prime 3142041103 := by
  apply lucas_primality 3142041103 (3 : ZMod 3142041103)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (174557839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (174557839, 1)] : List FactorBlock).map factorBlockValue).prod) = 3142041103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_174557839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3142041103) ^ 1571020551 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 3142041103) ^ 1047347034 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 3142041103) ^ 18 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_3232504679 : Nat.Prime 3232504679 := by
  apply lucas_primality 3232504679 (19 : ZMod 3232504679)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (73, 1), (100183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (73, 1), (100183, 1)] : List FactorBlock).map factorBlockValue).prod) = 3232504679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_73
      · exact prime_oneHundredFiftyOneES_100183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 3232504679) ^ 1616252339 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (19 : ZMod 3232504679) ^ 248654206 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (19 : ZMod 3232504679) ^ 190147334 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (19 : ZMod 3232504679) ^ 44280886 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (19 : ZMod 3232504679) ^ 32266 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_4263328073 : Nat.Prime 4263328073 := by
  apply lucas_primality 4263328073 (3 : ZMod 4263328073)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (31, 1), (904781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (31, 1), (904781, 1)] : List FactorBlock).map factorBlockValue).prod) = 4263328073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_904781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4263328073) ^ 2131664036 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 4263328073) ^ 224385688 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 4263328073) ^ 137526712 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 4263328073) ^ 4712 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_4472436259 : Nat.Prime 4472436259 := by
  apply lucas_primality 4472436259 (2 : ZMod 4472436259)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (13077299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (13077299, 1)] : List FactorBlock).map factorBlockValue).prod) = 4472436259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_13077299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4472436259) ^ 2236218129 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 4472436259) ^ 1490812086 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 4472436259) ^ 235391382 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 4472436259) ^ 342 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_4664345611 : Nat.Prime 4664345611 := by
  apply lucas_primality 4664345611 (7 : ZMod 4664345611)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2179, 1), (71353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2179, 1), (71353, 1)] : List FactorBlock).map factorBlockValue).prod) = 4664345611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_2179
      · exact prime_oneHundredFiftyOneES_71353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4664345611) ^ 2332172805 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 4664345611) ^ 1554781870 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 4664345611) ^ 932869122 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 4664345611) ^ 2140590 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 4664345611) ^ 65370 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_6027387371 : Nat.Prime 6027387371 := by
  apply lucas_primality 6027387371 (2 : ZMod 6027387371)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (11372429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (11372429, 1)] : List FactorBlock).map factorBlockValue).prod) = 6027387371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_53
      · exact prime_oneHundredFiftyOneES_11372429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6027387371) ^ 3013693685 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6027387371) ^ 1205477474 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6027387371) ^ 113724290 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6027387371) ^ 530 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_7113996457 : Nat.Prime 7113996457 := by
  apply lucas_primality 7113996457 (22 : ZMod 7113996457)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (349, 1), (121333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (349, 1), (121333, 1)] : List FactorBlock).map factorBlockValue).prod) = 7113996457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_349
      · exact prime_oneHundredFiftyOneES_121333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 7113996457) ^ 3556998228 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (22 : ZMod 7113996457) ^ 2371332152 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (22 : ZMod 7113996457) ^ 1016285208 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (22 : ZMod 7113996457) ^ 20383944 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (22 : ZMod 7113996457) ^ 58632 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_7861716307 : Nat.Prime 7861716307 := by
  apply lucas_primality 7861716307 (2 : ZMod 7861716307)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (127, 1), (127373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (127, 1), (127373, 1)] : List FactorBlock).map factorBlockValue).prod) = 7861716307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_127
      · exact prime_oneHundredFiftyOneES_127373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7861716307) ^ 3930858153 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7861716307) ^ 2620572102 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7861716307) ^ 61903278 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7861716307) ^ 61722 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_8196327617 : Nat.Prime 8196327617 := by
  apply lucas_primality 8196327617 (3 : ZMod 8196327617)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (19, 1), (37, 1), (67, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (19, 1), (37, 1), (67, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) = 8196327617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_37
      · exact prime_oneHundredFiftyOneES_67
      · exact prime_oneHundredFiftyOneES_2719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8196327617) ^ 4098163808 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 8196327617) ^ 431385664 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 8196327617) ^ 221522368 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 8196327617) ^ 122333248 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 8196327617) ^ 3014464 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_10227352969 : Nat.Prime 10227352969 := by
  apply lucas_primality 10227352969 (17 : ZMod 10227352969)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (20292367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (20292367, 1)] : List FactorBlock).map factorBlockValue).prod) = 10227352969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_20292367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 10227352969) ^ 5113676484 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 10227352969) ^ 3409117656 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 10227352969) ^ 1461050424 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 10227352969) ^ 504 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_11695448939 : Nat.Prime 11695448939 := by
  apply lucas_primality 11695448939 (2 : ZMod 11695448939)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2671, 1), (2189339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2671, 1), (2189339, 1)] : List FactorBlock).map factorBlockValue).prod) = 11695448939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_2671
      · exact prime_oneHundredFiftyOneES_2189339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11695448939) ^ 5847724469 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 11695448939) ^ 4378678 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 11695448939) ^ 5342 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_12021093817 : Nat.Prime 12021093817 := by
  apply lucas_primality 12021093817 (5 : ZMod 12021093817)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (500878909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (500878909, 1)] : List FactorBlock).map factorBlockValue).prod) = 12021093817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_500878909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12021093817) ^ 6010546908 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 12021093817) ^ 4007031272 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 12021093817) ^ 24 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_12489284641 : Nat.Prime 12489284641 := by
  apply lucas_primality 12489284641 (17 : ZMod 12489284641)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 2), (43, 1), (53, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 2), (43, 1), (53, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) = 12489284641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_43
      · exact prime_oneHundredFiftyOneES_53
      · exact prime_oneHundredFiftyOneES_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 12489284641) ^ 6244642320 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 12489284641) ^ 4163094880 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 12489284641) ^ 2497856928 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 12489284641) ^ 1784183520 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 12489284641) ^ 290448480 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 12489284641) ^ 235646880 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 12489284641) ^ 53602080 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_15982541437 : Nat.Prime 15982541437 := by
  apply lucas_primality 15982541437 (2 : ZMod 15982541437)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (2111, 1), (10343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (2111, 1), (10343, 1)] : List FactorBlock).map factorBlockValue).prod) = 15982541437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_61
      · exact prime_oneHundredFiftyOneES_2111
      · exact prime_oneHundredFiftyOneES_10343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15982541437) ^ 7991270718 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 15982541437) ^ 5327513812 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 15982541437) ^ 262008876 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 15982541437) ^ 7571076 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 15982541437) ^ 1545252 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_16566417313 : Nat.Prime 16566417313 := by
  apply lucas_primality 16566417313 (5 : ZMod 16566417313)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (587, 1), (17293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (587, 1), (17293, 1)] : List FactorBlock).map factorBlockValue).prod) = 16566417313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_587
      · exact prime_oneHundredFiftyOneES_17293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16566417313) ^ 8283208656 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 16566417313) ^ 5522139104 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 16566417313) ^ 974495136 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 16566417313) ^ 28222176 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 16566417313) ^ 957984 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_16577044457 : Nat.Prime 16577044457 := by
  apply lucas_primality 16577044457 (5 : ZMod 16577044457)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (15579929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (15579929, 1)] : List FactorBlock).map factorBlockValue).prod) = 16577044457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_15579929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16577044457) ^ 8288522228 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 16577044457) ^ 2368149208 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 16577044457) ^ 872476024 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 16577044457) ^ 1064 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_17976290363 : Nat.Prime 17976290363 := by
  apply lucas_primality 17976290363 (2 : ZMod 17976290363)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37897, 1), (237173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37897, 1), (237173, 1)] : List FactorBlock).map factorBlockValue).prod) = 17976290363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_37897
      · exact prime_oneHundredFiftyOneES_237173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17976290363) ^ 8988145181 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 17976290363) ^ 474346 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 17976290363) ^ 75794 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_18444336737 : Nat.Prime 18444336737 := by
  apply lucas_primality 18444336737 (3 : ZMod 18444336737)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (61, 1), (67, 1), (20147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (61, 1), (67, 1), (20147, 1)] : List FactorBlock).map factorBlockValue).prod) = 18444336737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_61
      · exact prime_oneHundredFiftyOneES_67
      · exact prime_oneHundredFiftyOneES_20147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18444336737) ^ 9222168368 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 18444336737) ^ 2634905248 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 18444336737) ^ 302366176 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 18444336737) ^ 275288608 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 18444336737) ^ 915488 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_18913945111 : Nat.Prime 18913945111 := by
  apply lucas_primality 18913945111 (3 : ZMod 18913945111)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4649, 1), (135613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4649, 1), (135613, 1)] : List FactorBlock).map factorBlockValue).prod) = 18913945111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_4649
      · exact prime_oneHundredFiftyOneES_135613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18913945111) ^ 9456972555 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 18913945111) ^ 6304648370 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 18913945111) ^ 3782789022 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 18913945111) ^ 4068390 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 18913945111) ^ 139470 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_19259561141 : Nat.Prime 19259561141 := by
  apply lucas_primality 19259561141 (2 : ZMod 19259561141)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (962978057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (962978057, 1)] : List FactorBlock).map factorBlockValue).prod) = 19259561141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_962978057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19259561141) ^ 9629780570 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 19259561141) ^ 3851912228 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 19259561141) ^ 20 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_20929484203 : Nat.Prime 20929484203 := by
  apply lucas_primality 20929484203 (11 : ZMod 20929484203)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (23, 1), (13787539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (23, 1), (13787539, 1)] : List FactorBlock).map factorBlockValue).prod) = 20929484203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_13787539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 20929484203) ^ 10464742101 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 20929484203) ^ 6976494734 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 20929484203) ^ 1902680382 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 20929484203) ^ 909977574 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 20929484203) ^ 1518 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_21652755073 : Nat.Prime 21652755073 := by
  apply lucas_primality 21652755073 (5 : ZMod 21652755073)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (19, 1), (167, 1), (1367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (19, 1), (167, 1), (1367, 1)] : List FactorBlock).map factorBlockValue).prod) = 21652755073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_167
      · exact prime_oneHundredFiftyOneES_1367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21652755073) ^ 10826377536 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 21652755073) ^ 7217585024 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 21652755073) ^ 1665596544 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 21652755073) ^ 1139618688 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 21652755073) ^ 129657216 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 21652755073) ^ 15839616 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_22961446511 : Nat.Prime 22961446511 := by
  apply lucas_primality 22961446511 (17 : ZMod 22961446511)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (163, 1), (461, 1), (30557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (163, 1), (461, 1), (30557, 1)] : List FactorBlock).map factorBlockValue).prod) = 22961446511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_163
      · exact prime_oneHundredFiftyOneES_461
      · exact prime_oneHundredFiftyOneES_30557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 22961446511) ^ 11480723255 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 22961446511) ^ 4592289302 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 22961446511) ^ 140867770 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 22961446511) ^ 49807910 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (17 : ZMod 22961446511) ^ 751430 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_23390897879 : Nat.Prime 23390897879 := by
  apply lucas_primality 23390897879 (13 : ZMod 23390897879)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11695448939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11695448939, 1)] : List FactorBlock).map factorBlockValue).prod) = 23390897879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11695448939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 23390897879) ^ 11695448939 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 23390897879) ^ 2 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_25423096883 : Nat.Prime 25423096883 := by
  apply lucas_primality 25423096883 (2 : ZMod 25423096883)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1579, 1), (8050379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1579, 1), (8050379, 1)] : List FactorBlock).map factorBlockValue).prod) = 25423096883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_1579
      · exact prime_oneHundredFiftyOneES_8050379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25423096883) ^ 12711548441 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 25423096883) ^ 16100758 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 25423096883) ^ 3158 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_26365356943 : Nat.Prime 26365356943 := by
  apply lucas_primality 26365356943 (5 : ZMod 26365356943)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4027, 1), (1091191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4027, 1), (1091191, 1)] : List FactorBlock).map factorBlockValue).prod) = 26365356943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_4027
      · exact prime_oneHundredFiftyOneES_1091191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 26365356943) ^ 13182678471 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 26365356943) ^ 8788452314 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 26365356943) ^ 6547146 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 26365356943) ^ 24162 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_27233688743 : Nat.Prime 27233688743 := by
  apply lucas_primality 27233688743 (5 : ZMod 27233688743)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (47, 1), (22286161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (47, 1), (22286161, 1)] : List FactorBlock).map factorBlockValue).prod) = 27233688743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_47
      · exact prime_oneHundredFiftyOneES_22286161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27233688743) ^ 13616844371 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 27233688743) ^ 2094899134 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 27233688743) ^ 579440186 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 27233688743) ^ 1222 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_29612907889 : Nat.Prime 29612907889 := by
  apply lucas_primality 29612907889 (7 : ZMod 29612907889)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (616935581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (616935581, 1)] : List FactorBlock).map factorBlockValue).prod) = 29612907889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_616935581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 29612907889) ^ 14806453944 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 29612907889) ^ 9870969296 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 29612907889) ^ 48 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_31209357691 : Nat.Prime 31209357691 := by
  apply lucas_primality 31209357691 (2 : ZMod 31209357691)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (17, 1), (337, 1), (8647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (17, 1), (337, 1), (8647, 1)] : List FactorBlock).map factorBlockValue).prod) = 31209357691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_337
      · exact prime_oneHundredFiftyOneES_8647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31209357691) ^ 15604678845 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 31209357691) ^ 10403119230 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 31209357691) ^ 6241871538 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 31209357691) ^ 4458479670 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 31209357691) ^ 1835844570 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 31209357691) ^ 92609370 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 31209357691) ^ 3609270 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_33465491909 : Nat.Prime 33465491909 := by
  apply lucas_primality 33465491909 (2 : ZMod 33465491909)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (114607849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (114607849, 1)] : List FactorBlock).map factorBlockValue).prod) = 33465491909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_73
      · exact prime_oneHundredFiftyOneES_114607849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33465491909) ^ 16732745954 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 33465491909) ^ 458431396 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 33465491909) ^ 292 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_36814847039 : Nat.Prime 36814847039 := by
  apply lucas_primality 36814847039 (11 : ZMod 36814847039)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (233005361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (233005361, 1)] : List FactorBlock).map factorBlockValue).prod) = 36814847039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_79
      · exact prime_oneHundredFiftyOneES_233005361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 36814847039) ^ 18407423519 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 36814847039) ^ 466010722 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 36814847039) ^ 158 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_37155304699 : Nat.Prime 37155304699 := by
  apply lucas_primality 37155304699 (3 : ZMod 37155304699)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (277, 1), (22355779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (277, 1), (22355779, 1)] : List FactorBlock).map factorBlockValue).prod) = 37155304699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_277
      · exact prime_oneHundredFiftyOneES_22355779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37155304699) ^ 18577652349 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 37155304699) ^ 12385101566 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 37155304699) ^ 134134674 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 37155304699) ^ 1662 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_37819401857 : Nat.Prime 37819401857 := by
  apply lucas_primality 37819401857 (3 : ZMod 37819401857)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (4651, 1), (63527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (4651, 1), (63527, 1)] : List FactorBlock).map factorBlockValue).prod) = 37819401857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_4651
      · exact prime_oneHundredFiftyOneES_63527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 37819401857) ^ 18909700928 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 37819401857) ^ 8131456 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 37819401857) ^ 595328 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_43901846147 : Nat.Prime 43901846147 := by
  apply lucas_primality 43901846147 (5 : ZMod 43901846147)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (10079, 1), (128111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (10079, 1), (128111, 1)] : List FactorBlock).map factorBlockValue).prod) = 43901846147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_10079
      · exact prime_oneHundredFiftyOneES_128111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 43901846147) ^ 21950923073 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 43901846147) ^ 2582461538 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 43901846147) ^ 4355774 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 43901846147) ^ 342686 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_44483953993 : Nat.Prime 44483953993 := by
  apply lucas_primality 44483953993 (5 : ZMod 44483953993)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (29, 1), (1877, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (29, 1), (1877, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) = 44483953993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_1877
      · exact prime_oneHundredFiftyOneES_2003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44483953993) ^ 22241976996 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 44483953993) ^ 14827984664 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 44483953993) ^ 2616703176 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 44483953993) ^ 1533929448 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 44483953993) ^ 23699496 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 44483953993) ^ 22208664 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_48639818621 : Nat.Prime 48639818621 := by
  apply lucas_primality 48639818621 (10 : ZMod 48639818621)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (10133, 1), (240007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (10133, 1), (240007, 1)] : List FactorBlock).map factorBlockValue).prod) = 48639818621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_10133
      · exact prime_oneHundredFiftyOneES_240007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 48639818621) ^ 24319909310 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 48639818621) ^ 9727963724 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 48639818621) ^ 4800140 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 48639818621) ^ 202660 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_49140608417 : Nat.Prime 49140608417 := by
  apply lucas_primality 49140608417 (3 : ZMod 49140608417)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (66767131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (66767131, 1)] : List FactorBlock).map factorBlockValue).prod) = 49140608417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_66767131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 49140608417) ^ 24570304208 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 49140608417) ^ 2136548192 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 49140608417) ^ 736 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_50955035233 : Nat.Prime 50955035233 := by
  apply lucas_primality 50955035233 (5 : ZMod 50955035233)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (2903, 1), (182839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (2903, 1), (182839, 1)] : List FactorBlock).map factorBlockValue).prod) = 50955035233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_2903
      · exact prime_oneHundredFiftyOneES_182839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 50955035233) ^ 25477517616 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 50955035233) ^ 16985011744 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 50955035233) ^ 17552544 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 50955035233) ^ 278688 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_73629694079 : Nat.Prime 73629694079 := by
  apply lucas_primality 73629694079 (7 : ZMod 73629694079)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (36814847039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (36814847039, 1)] : List FactorBlock).map factorBlockValue).prod) = 73629694079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_36814847039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 73629694079) ^ 36814847039 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 73629694079) ^ 2 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_86676901291 : Nat.Prime 86676901291 := by
  apply lucas_primality 86676901291 (7 : ZMod 86676901291)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (137582383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (137582383, 1)] : List FactorBlock).map factorBlockValue).prod) = 86676901291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_137582383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 86676901291) ^ 43338450645 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 86676901291) ^ 28892300430 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 86676901291) ^ 17335380258 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 86676901291) ^ 12382414470 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 86676901291) ^ 630 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_87443994667 : Nat.Prime 87443994667 := by
  apply lucas_primality 87443994667 (2 : ZMod 87443994667)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (103, 1), (383, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (103, 1), (383, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) = 87443994667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_89
      · exact prime_oneHundredFiftyOneES_103
      · exact prime_oneHundredFiftyOneES_383
      · exact prime_oneHundredFiftyOneES_593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 87443994667) ^ 43721997333 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 87443994667) ^ 29147998222 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 87443994667) ^ 12491999238 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 87443994667) ^ 982516794 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 87443994667) ^ 848970822 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 87443994667) ^ 228313302 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 87443994667) ^ 147460362 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_95825264243 : Nat.Prime 95825264243 := by
  apply lucas_primality 95825264243 (2 : ZMod 95825264243)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (853, 1), (198479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (853, 1), (198479, 1)] : List FactorBlock).map factorBlockValue).prod) = 95825264243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_283
      · exact prime_oneHundredFiftyOneES_853
      · exact prime_oneHundredFiftyOneES_198479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 95825264243) ^ 47912632121 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 95825264243) ^ 338605174 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 95825264243) ^ 112339114 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 95825264243) ^ 482798 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_102273529691 : Nat.Prime 102273529691 := by
  apply lucas_primality 102273529691 (2 : ZMod 102273529691)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10227352969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10227352969, 1)] : List FactorBlock).map factorBlockValue).prod) = 102273529691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_10227352969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 102273529691) ^ 51136764845 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 102273529691) ^ 20454705938 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 102273529691) ^ 10 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_103756513691 : Nat.Prime 103756513691 := by
  apply lucas_primality 103756513691 (2 : ZMod 103756513691)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1033, 1), (10044193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1033, 1), (10044193, 1)] : List FactorBlock).map factorBlockValue).prod) = 103756513691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_1033
      · exact prime_oneHundredFiftyOneES_10044193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 103756513691) ^ 51878256845 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 103756513691) ^ 20751302738 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 103756513691) ^ 100441930 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 103756513691) ^ 10330 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_144006175589 : Nat.Prime 144006175589 := by
  apply lucas_primality 144006175589 (7 : ZMod 144006175589)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (11093, 1), (295039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (11093, 1), (295039, 1)] : List FactorBlock).map factorBlockValue).prod) = 144006175589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_11093
      · exact prime_oneHundredFiftyOneES_295039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 144006175589) ^ 72003087794 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 144006175589) ^ 13091470508 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 144006175589) ^ 12981716 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 144006175589) ^ 488092 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_159205033769 : Nat.Prime 159205033769 := by
  apply lucas_primality 159205033769 (3 : ZMod 159205033769)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (47, 1), (79, 1), (487247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (47, 1), (79, 1), (487247, 1)] : List FactorBlock).map factorBlockValue).prod) = 159205033769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_47
      · exact prime_oneHundredFiftyOneES_79
      · exact prime_oneHundredFiftyOneES_487247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 159205033769) ^ 79602516884 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 159205033769) ^ 14473184888 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 159205033769) ^ 3387341144 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 159205033769) ^ 2015253592 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 159205033769) ^ 326744 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_165580895497 : Nat.Prime 165580895497 := by
  apply lucas_primality 165580895497 (11 : ZMod 165580895497)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (139, 1), (49634561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (139, 1), (49634561, 1)] : List FactorBlock).map factorBlockValue).prod) = 165580895497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_139
      · exact prime_oneHundredFiftyOneES_49634561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 165580895497) ^ 82790447748 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 165580895497) ^ 55193631832 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 165580895497) ^ 1191229464 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 165580895497) ^ 3336 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_176249999227 : Nat.Prime 176249999227 := by
  apply lucas_primality 176249999227 (2 : ZMod 176249999227)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (31, 1), (397, 1), (340979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (31, 1), (397, 1), (340979, 1)] : List FactorBlock).map factorBlockValue).prod) = 176249999227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_397
      · exact prime_oneHundredFiftyOneES_340979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 176249999227) ^ 88124999613 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 176249999227) ^ 58749999742 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 176249999227) ^ 25178571318 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 176249999227) ^ 5685483846 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 176249999227) ^ 443954658 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 176249999227) ^ 516894 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_190899756349 : Nat.Prime 190899756349 := by
  apply lucas_primality 190899756349 (2 : ZMod 190899756349)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (79, 1), (881, 1), (32653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (79, 1), (881, 1), (32653, 1)] : List FactorBlock).map factorBlockValue).prod) = 190899756349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_79
      · exact prime_oneHundredFiftyOneES_881
      · exact prime_oneHundredFiftyOneES_32653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 190899756349) ^ 95449878174 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 190899756349) ^ 63633252116 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 190899756349) ^ 27271393764 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 190899756349) ^ 2416452612 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 190899756349) ^ 216685308 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 190899756349) ^ 5846316 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_198779948347 : Nat.Prime 198779948347 := by
  apply lucas_primality 198779948347 (2 : ZMod 198779948347)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (97, 1), (463, 1), (6199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (97, 1), (463, 1), (6199, 1)] : List FactorBlock).map factorBlockValue).prod) = 198779948347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_97
      · exact prime_oneHundredFiftyOneES_463
      · exact prime_oneHundredFiftyOneES_6199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 198779948347) ^ 99389974173 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 198779948347) ^ 66259982782 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 198779948347) ^ 28397135478 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 198779948347) ^ 11692938138 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 198779948347) ^ 2049277818 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 198779948347) ^ 429330342 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 198779948347) ^ 32066454 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_204547059383 : Nat.Prime 204547059383 := by
  apply lucas_primality 204547059383 (5 : ZMod 204547059383)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (102273529691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (102273529691, 1)] : List FactorBlock).map factorBlockValue).prod) = 204547059383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_102273529691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 204547059383) ^ 102273529691 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 204547059383) ^ 2 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_208010024081 : Nat.Prime 208010024081 := by
  apply lucas_primality 208010024081 (3 : ZMod 208010024081)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (2600125301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (2600125301, 1)] : List FactorBlock).map factorBlockValue).prod) = 208010024081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_2600125301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 208010024081) ^ 104005012040 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 208010024081) ^ 41602004816 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 208010024081) ^ 80 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_312230232239 : Nat.Prime 312230232239 := by
  apply lucas_primality 312230232239 (7 : ZMod 312230232239)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (101, 1), (317, 1), (118927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (101, 1), (317, 1), (118927, 1)] : List FactorBlock).map factorBlockValue).prod) = 312230232239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_41
      · exact prime_oneHundredFiftyOneES_101
      · exact prime_oneHundredFiftyOneES_317
      · exact prime_oneHundredFiftyOneES_118927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 312230232239) ^ 156115116119 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 312230232239) ^ 7615371518 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 312230232239) ^ 3091388438 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 312230232239) ^ 984953414 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 312230232239) ^ 2625394 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_318410067539 : Nat.Prime 318410067539 := by
  apply lucas_primality 318410067539 (2 : ZMod 318410067539)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (159205033769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (159205033769, 1)] : List FactorBlock).map factorBlockValue).prod) = 318410067539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_159205033769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 318410067539) ^ 159205033769 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 318410067539) ^ 2 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_405865850597 : Nat.Prime 405865850597 := by
  apply lucas_primality 405865850597 (2 : ZMod 405865850597)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (52639, 1), (1927591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (52639, 1), (1927591, 1)] : List FactorBlock).map factorBlockValue).prod) = 405865850597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_52639
      · exact prime_oneHundredFiftyOneES_1927591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 405865850597) ^ 202932925298 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 405865850597) ^ 7710364 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 405865850597) ^ 210556 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_570854197619 : Nat.Prime 570854197619 := by
  apply lucas_primality 570854197619 (2 : ZMod 570854197619)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18077, 1), (15789517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18077, 1), (15789517, 1)] : List FactorBlock).map factorBlockValue).prod) = 570854197619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_18077
      · exact prime_oneHundredFiftyOneES_15789517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 570854197619) ^ 285427098809 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 570854197619) ^ 31579034 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 570854197619) ^ 36154 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_708924783013 : Nat.Prime 708924783013 := by
  apply lucas_primality 708924783013 (2 : ZMod 708924783013)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3169, 1), (18642179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3169, 1), (18642179, 1)] : List FactorBlock).map factorBlockValue).prod) = 708924783013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_3169
      · exact prime_oneHundredFiftyOneES_18642179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 708924783013) ^ 354462391506 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 708924783013) ^ 236308261004 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 708924783013) ^ 223706148 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 708924783013) ^ 38028 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_874459818989 : Nat.Prime 874459818989 := by
  apply lucas_primality 874459818989 (2 : ZMod 874459818989)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (41, 1), (7243, 1), (105167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (41, 1), (7243, 1), (105167, 1)] : List FactorBlock).map factorBlockValue).prod) = 874459818989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_41
      · exact prime_oneHundredFiftyOneES_7243
      · exact prime_oneHundredFiftyOneES_105167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 874459818989) ^ 437229909494 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 874459818989) ^ 124922831284 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 874459818989) ^ 21328288268 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 874459818989) ^ 120731716 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 874459818989) ^ 8314964 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_875516735179 : Nat.Prime 875516735179 := by
  apply lucas_primality 875516735179 (3 : ZMod 875516735179)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (48639818621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (48639818621, 1)] : List FactorBlock).map factorBlockValue).prod) = 875516735179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_48639818621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 875516735179) ^ 437758367589 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 875516735179) ^ 291838911726 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 875516735179) ^ 18 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_917920329097 : Nat.Prime 917920329097 := by
  apply lucas_primality 917920329097 (5 : ZMod 917920329097)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (15937, 1), (51061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (15937, 1), (51061, 1)] : List FactorBlock).map factorBlockValue).prod) = 917920329097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_47
      · exact prime_oneHundredFiftyOneES_15937
      · exact prime_oneHundredFiftyOneES_51061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 917920329097) ^ 458960164548 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 917920329097) ^ 305973443032 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 917920329097) ^ 19530219768 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 917920329097) ^ 57596808 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 917920329097) ^ 17976936 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_993922562527 : Nat.Prime 993922562527 := by
  apply lucas_primality 993922562527 (3 : ZMod 993922562527)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (151, 1), (4157, 1), (8513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (151, 1), (4157, 1), (8513, 1)] : List FactorBlock).map factorBlockValue).prod) = 993922562527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_151
      · exact prime_oneHundredFiftyOneES_4157
      · exact prime_oneHundredFiftyOneES_8513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 993922562527) ^ 496961281263 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 993922562527) ^ 331307520842 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 993922562527) ^ 32062018146 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 993922562527) ^ 6582268626 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 993922562527) ^ 239096118 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 993922562527) ^ 116753502 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1064868935041 : Nat.Prime 1064868935041 := by
  apply lucas_primality 1064868935041 (13 : ZMod 1064868935041)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 1), (17, 1), (10874887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 1), (17, 1), (10874887, 1)] : List FactorBlock).map factorBlockValue).prod) = 1064868935041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_10874887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1064868935041) ^ 532434467520 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 1064868935041) ^ 354956311680 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 1064868935041) ^ 212973787008 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 1064868935041) ^ 62639349120 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 1064868935041) ^ 97920 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1121010775127 : Nat.Prime 1121010775127 := by
  apply lucas_primality 1121010775127 (5 : ZMod 1121010775127)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (50955035233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (50955035233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1121010775127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_50955035233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1121010775127) ^ 560505387563 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121010775127) ^ 101910070466 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 1121010775127) ^ 22 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1325334493423 : Nat.Prime 1325334493423 := by
  apply lucas_primality 1325334493423 (5 : ZMod 1325334493423)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73629694079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73629694079, 1)] : List FactorBlock).map factorBlockValue).prod) = 1325334493423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_73629694079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1325334493423) ^ 662667246711 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 1325334493423) ^ 441778164474 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 1325334493423) ^ 18 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1654005481679 : Nat.Prime 1654005481679 := by
  apply lucas_primality 1654005481679 (11 : ZMod 1654005481679)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (31, 1), (773, 1), (108187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (31, 1), (773, 1), (108187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1654005481679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_773
      · exact prime_oneHundredFiftyOneES_108187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1654005481679) ^ 827002740839 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 1654005481679) ^ 150364134698 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 1654005481679) ^ 57034671782 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 1654005481679) ^ 53355015538 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 1654005481679) ^ 2139722486 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 1654005481679) ^ 15288394 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1767329843863 : Nat.Prime 1767329843863 := by
  apply lucas_primality 1767329843863 (6 : ZMod 1767329843863)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (23, 1), (1164248909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (23, 1), (1164248909, 1)] : List FactorBlock).map factorBlockValue).prod) = 1767329843863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_1164248909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1767329843863) ^ 883664921931 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 1767329843863) ^ 589109947954 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 1767329843863) ^ 160666349442 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 1767329843863) ^ 76840427994 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 1767329843863) ^ 1518 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1867343119847 : Nat.Prime 1867343119847 := by
  apply lucas_primality 1867343119847 (5 : ZMod 1867343119847)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (49140608417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (49140608417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1867343119847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_49140608417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1867343119847) ^ 933671559923 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 1867343119847) ^ 98281216834 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 1867343119847) ^ 38 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1880462109161 : Nat.Prime 1880462109161 := by
  apply lucas_primality 1880462109161 (6 : ZMod 1880462109161)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (73, 1), (11587, 1), (55579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (73, 1), (11587, 1), (55579, 1)] : List FactorBlock).map factorBlockValue).prod) = 1880462109161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_73
      · exact prime_oneHundredFiftyOneES_11587
      · exact prime_oneHundredFiftyOneES_55579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1880462109161) ^ 940231054580 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 1880462109161) ^ 376092421832 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 1880462109161) ^ 25759754920 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 1880462109161) ^ 162290680 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 1880462109161) ^ 33834040 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2025695619919 : Nat.Prime 2025695619919 := by
  apply lucas_primality 2025695619919 (3 : ZMod 2025695619919)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (607, 1), (185401393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (607, 1), (185401393, 1)] : List FactorBlock).map factorBlockValue).prod) = 2025695619919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_607
      · exact prime_oneHundredFiftyOneES_185401393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2025695619919) ^ 1012847809959 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2025695619919) ^ 675231873306 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2025695619919) ^ 3337225074 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2025695619919) ^ 10926 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2463086489011 : Nat.Prime 2463086489011 := by
  apply lucas_primality 2463086489011 (3 : ZMod 2463086489011)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (89, 1), (7752137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (89, 1), (7752137, 1)] : List FactorBlock).map factorBlockValue).prod) = 2463086489011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_89
      · exact prime_oneHundredFiftyOneES_7752137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2463086489011) ^ 1231543244505 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2463086489011) ^ 821028829670 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2463086489011) ^ 492617297802 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2463086489011) ^ 351869498430 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2463086489011) ^ 144887440530 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2463086489011) ^ 27675129090 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2463086489011) ^ 317730 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2547280540313 : Nat.Prime 2547280540313 := by
  apply lucas_primality 2547280540313 (3 : ZMod 2547280540313)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (318410067539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (318410067539, 1)] : List FactorBlock).map factorBlockValue).prod) = 2547280540313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_318410067539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2547280540313) ^ 1273640270156 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2547280540313) ^ 8 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2617313696161 : Nat.Prime 2617313696161 := by
  apply lucas_primality 2617313696161 (11 : ZMod 2617313696161)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (10993, 1), (496019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (10993, 1), (496019, 1)] : List FactorBlock).map factorBlockValue).prod) = 2617313696161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_10993
      · exact prime_oneHundredFiftyOneES_496019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2617313696161) ^ 1308656848080 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 2617313696161) ^ 872437898720 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 2617313696161) ^ 523462739232 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 2617313696161) ^ 238089120 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 2617313696161) ^ 5276640 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2916780057839 : Nat.Prime 2916780057839 := by
  apply lucas_primality 2916780057839 (7 : ZMod 2916780057839)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (94907, 1), (229351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (94907, 1), (229351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2916780057839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_67
      · exact prime_oneHundredFiftyOneES_94907
      · exact prime_oneHundredFiftyOneES_229351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2916780057839) ^ 1458390028919 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 2916780057839) ^ 43534030714 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 2916780057839) ^ 30733034 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 2916780057839) ^ 12717538 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2979277546433 : Nat.Prime 2979277546433 := by
  apply lucas_primality 2979277546433 (3 : ZMod 2979277546433)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (11, 1), (73, 1), (57971621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (11, 1), (73, 1), (57971621, 1)] : List FactorBlock).map factorBlockValue).prod) = 2979277546433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_73
      · exact prime_oneHundredFiftyOneES_57971621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2979277546433) ^ 1489638773216 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2979277546433) ^ 270843413312 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2979277546433) ^ 40812021184 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2979277546433) ^ 51392 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_4958870350349 : Nat.Prime 4958870350349 := by
  apply lucas_primality 4958870350349 (2 : ZMod 4958870350349)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (23390897879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (23390897879, 1)] : List FactorBlock).map factorBlockValue).prod) = 4958870350349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_53
      · exact prime_oneHundredFiftyOneES_23390897879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4958870350349) ^ 2479435175174 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 4958870350349) ^ 93563591516 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 4958870350349) ^ 212 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_5077141237451 : Nat.Prime 5077141237451 := by
  apply lucas_primality 5077141237451 (6 : ZMod 5077141237451)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (199, 1), (487, 1), (1047773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (199, 1), (487, 1), (1047773, 1)] : List FactorBlock).map factorBlockValue).prod) = 5077141237451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_199
      · exact prime_oneHundredFiftyOneES_487
      · exact prime_oneHundredFiftyOneES_1047773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5077141237451) ^ 2538570618725 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 5077141237451) ^ 1015428247490 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 5077141237451) ^ 25513272550 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 5077141237451) ^ 10425341350 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 5077141237451) ^ 4845650 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_5948495845393 : Nat.Prime 5948495845393 := by
  apply lucas_primality 5948495845393 (7 : ZMod 5948495845393)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (131, 1), (991, 1), (954599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (131, 1), (991, 1), (954599, 1)] : List FactorBlock).map factorBlockValue).prod) = 5948495845393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_131
      · exact prime_oneHundredFiftyOneES_991
      · exact prime_oneHundredFiftyOneES_954599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5948495845393) ^ 2974247922696 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 5948495845393) ^ 1982831948464 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 5948495845393) ^ 45408365232 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 5948495845393) ^ 6002518512 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 5948495845393) ^ 6231408 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_7139212081039 : Nat.Prime 7139212081039 := by
  apply lucas_primality 7139212081039 (3 : ZMod 7139212081039)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (107, 1), (44659711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (107, 1), (44659711, 1)] : List FactorBlock).map factorBlockValue).prod) = 7139212081039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_83
      · exact prime_oneHundredFiftyOneES_107
      · exact prime_oneHundredFiftyOneES_44659711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7139212081039) ^ 3569606040519 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 7139212081039) ^ 2379737360346 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 7139212081039) ^ 86014603386 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 7139212081039) ^ 66721608234 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 7139212081039) ^ 159858 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_13068837977309 : Nat.Prime 13068837977309 := by
  apply lucas_primality 13068837977309 (2 : ZMod 13068837977309)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (457, 1), (174372071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (457, 1), (174372071, 1)] : List FactorBlock).map factorBlockValue).prod) = 13068837977309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_41
      · exact prime_oneHundredFiftyOneES_457
      · exact prime_oneHundredFiftyOneES_174372071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13068837977309) ^ 6534418988654 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 13068837977309) ^ 318752145788 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 13068837977309) ^ 28597019644 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 13068837977309) ^ 74948 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_13143014873179 : Nat.Prime 13143014873179 := by
  apply lucas_primality 13143014873179 (2 : ZMod 13143014873179)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (163811, 1), (361409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (163811, 1), (361409, 1)] : List FactorBlock).map factorBlockValue).prod) = 13143014873179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_37
      · exact prime_oneHundredFiftyOneES_163811
      · exact prime_oneHundredFiftyOneES_361409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13143014873179) ^ 6571507436589 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 13143014873179) ^ 4381004957726 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 13143014873179) ^ 355216618194 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 13143014873179) ^ 80232798 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 13143014873179) ^ 36366042 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_13336428476911 : Nat.Prime 13336428476911 := by
  apply lucas_primality 13336428476911 (6 : ZMod 13336428476911)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (557, 1), (1733, 1), (5981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (557, 1), (1733, 1), (5981, 1)] : List FactorBlock).map factorBlockValue).prod) = 13336428476911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_557
      · exact prime_oneHundredFiftyOneES_1733
      · exact prime_oneHundredFiftyOneES_5981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 13336428476911) ^ 6668214238455 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 13336428476911) ^ 4445476158970 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 13336428476911) ^ 2667285695382 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 13336428476911) ^ 1905204068130 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 13336428476911) ^ 1212402588810 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 13336428476911) ^ 23943318630 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 13336428476911) ^ 7695573270 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 13336428476911) ^ 2229799110 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_14669408552507 : Nat.Prime 14669408552507 := by
  apply lucas_primality 14669408552507 (2 : ZMod 14669408552507)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (311, 1), (4283, 1), (5506481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (311, 1), (4283, 1), (5506481, 1)] : List FactorBlock).map factorBlockValue).prod) = 14669408552507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_311
      · exact prime_oneHundredFiftyOneES_4283
      · exact prime_oneHundredFiftyOneES_5506481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14669408552507) ^ 7334704276253 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 14669408552507) ^ 47168516246 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 14669408552507) ^ 3425031182 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 14669408552507) ^ 2664026 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_15902761000433 : Nat.Prime 15902761000433 := by
  apply lucas_primality 15902761000433 (3 : ZMod 15902761000433)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (993922562527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (993922562527, 1)] : List FactorBlock).map factorBlockValue).prod) = 15902761000433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_993922562527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 15902761000433) ^ 7951380500216 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 15902761000433) ^ 16 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_17211691285577 : Nat.Prime 17211691285577 := by
  apply lucas_primality 17211691285577 (3 : ZMod 17211691285577)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (79, 1), (27233688743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (79, 1), (27233688743, 1)] : List FactorBlock).map factorBlockValue).prod) = 17211691285577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_79
      · exact prime_oneHundredFiftyOneES_27233688743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17211691285577) ^ 8605845642788 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 17211691285577) ^ 217869509944 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 17211691285577) ^ 632 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_17427170532859 : Nat.Prime 17427170532859 := by
  apply lucas_primality 17427170532859 (2 : ZMod 17427170532859)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1789, 1), (70589069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1789, 1), (70589069, 1)] : List FactorBlock).map factorBlockValue).prod) = 17427170532859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_1789
      · exact prime_oneHundredFiftyOneES_70589069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17427170532859) ^ 8713585266429 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 17427170532859) ^ 5809056844286 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 17427170532859) ^ 757703066646 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 17427170532859) ^ 9741291522 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 17427170532859) ^ 246882 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_22869556676257 : Nat.Prime 22869556676257 := by
  apply lucas_primality 22869556676257 (5 : ZMod 22869556676257)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (113, 1), (2459, 1), (857333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (113, 1), (2459, 1), (857333, 1)] : List FactorBlock).map factorBlockValue).prod) = 22869556676257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_113
      · exact prime_oneHundredFiftyOneES_2459
      · exact prime_oneHundredFiftyOneES_857333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22869556676257) ^ 11434778338128 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 22869556676257) ^ 7623185558752 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 22869556676257) ^ 202385457312 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 22869556676257) ^ 9300348384 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 22869556676257) ^ 26675232 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_25701497786113 : Nat.Prime 25701497786113 := by
  apply lucas_primality 25701497786113 (5 : ZMod 25701497786113)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (33465491909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (33465491909, 1)] : List FactorBlock).map factorBlockValue).prod) = 25701497786113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_33465491909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 25701497786113) ^ 12850748893056 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 25701497786113) ^ 8567165928704 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 25701497786113) ^ 768 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_32629185343309 : Nat.Prime 32629185343309 := by
  apply lucas_primality 32629185343309 (2 : ZMod 32629185343309)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (1879, 1), (85123463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (1879, 1), (85123463, 1)] : List FactorBlock).map factorBlockValue).prod) = 32629185343309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_1879
      · exact prime_oneHundredFiftyOneES_85123463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32629185343309) ^ 16314592671654 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 32629185343309) ^ 10876395114436 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 32629185343309) ^ 1919363843724 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 32629185343309) ^ 17365186452 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 32629185343309) ^ 383316 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_35562897139823 : Nat.Prime 35562897139823 := by
  apply lucas_primality 35562897139823 (5 : ZMod 35562897139823)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (4513, 1), (4691, 1), (64609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (4513, 1), (4691, 1), (64609, 1)] : List FactorBlock).map factorBlockValue).prod) = 35562897139823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_4513
      · exact prime_oneHundredFiftyOneES_4691
      · exact prime_oneHundredFiftyOneES_64609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 35562897139823) ^ 17781448569911 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 35562897139823) ^ 2735607472294 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 35562897139823) ^ 7880101294 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 35562897139823) ^ 7581090842 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 35562897139823) ^ 550432558 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_35661927564383 : Nat.Prime 35661927564383 := by
  apply lucas_primality 35661927564383 (5 : ZMod 35661927564383)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2547280540313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2547280540313, 1)] : List FactorBlock).map factorBlockValue).prod) = 35661927564383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_2547280540313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 35661927564383) ^ 17830963782191 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 35661927564383) ^ 5094561080626 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 35661927564383) ^ 14 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_48295580432977 : Nat.Prime 48295580432977 := by
  apply lucas_primality 48295580432977 (5 : ZMod 48295580432977)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (23, 1), (37, 1), (394108079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (23, 1), (37, 1), (394108079, 1)] : List FactorBlock).map factorBlockValue).prod) = 48295580432977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_37
      · exact prime_oneHundredFiftyOneES_394108079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 48295580432977) ^ 24147790216488 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 48295580432977) ^ 16098526810992 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 48295580432977) ^ 2099807844912 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 48295580432977) ^ 1305285957648 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 48295580432977) ^ 122544 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_50514094095523 : Nat.Prime 50514094095523 := by
  apply lucas_primality 50514094095523 (2 : ZMod 50514094095523)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (38153, 1), (220664579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (38153, 1), (220664579, 1)] : List FactorBlock).map factorBlockValue).prod) = 50514094095523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_38153
      · exact prime_oneHundredFiftyOneES_220664579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50514094095523) ^ 25257047047761 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 50514094095523) ^ 16838031365174 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 50514094095523) ^ 1323987474 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 50514094095523) ^ 228918 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_71323855128767 : Nat.Prime 71323855128767 := by
  apply lucas_primality 71323855128767 (5 : ZMod 71323855128767)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (35661927564383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (35661927564383, 1)] : List FactorBlock).map factorBlockValue).prod) = 71323855128767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_35661927564383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 71323855128767) ^ 35661927564383 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 71323855128767) ^ 2 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_71892124424777 : Nat.Prime 71892124424777 := by
  apply lucas_primality 71892124424777 (3 : ZMod 71892124424777)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (8867, 1), (32692861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (8867, 1), (32692861, 1)] : List FactorBlock).map factorBlockValue).prod) = 71892124424777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_8867
      · exact prime_oneHundredFiftyOneES_32692861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 71892124424777) ^ 35946062212388 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 71892124424777) ^ 2319100787896 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 71892124424777) ^ 8107829528 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 71892124424777) ^ 2199016 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_102341175912377 : Nat.Prime 102341175912377 := by
  apply lucas_primality 102341175912377 (3 : ZMod 102341175912377)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (118621, 1), (3718783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (118621, 1), (3718783, 1)] : List FactorBlock).map factorBlockValue).prod) = 102341175912377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_118621
      · exact prime_oneHundredFiftyOneES_3718783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 102341175912377) ^ 51170587956188 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 102341175912377) ^ 3529006065944 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 102341175912377) ^ 862757656 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 102341175912377) ^ 27520072 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_128505817458703 : Nat.Prime 128505817458703 := by
  apply lucas_primality 128505817458703 (5 : ZMod 128505817458703)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7139212081039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7139212081039, 1)] : List FactorBlock).map factorBlockValue).prod) = 128505817458703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7139212081039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 128505817458703) ^ 64252908729351 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 128505817458703) ^ 42835272486234 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 128505817458703) ^ 18 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_132769719345253 : Nat.Prime 132769719345253 := by
  apply lucas_primality 132769719345253 (5 : ZMod 132769719345253)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (269, 1), (2311, 1), (147089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (269, 1), (2311, 1), (147089, 1)] : List FactorBlock).map factorBlockValue).prod) = 132769719345253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_269
      · exact prime_oneHundredFiftyOneES_2311
      · exact prime_oneHundredFiftyOneES_147089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 132769719345253) ^ 66384859672626 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 132769719345253) ^ 44256573115084 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 132769719345253) ^ 12069974485932 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 132769719345253) ^ 493567729908 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 132769719345253) ^ 57451198332 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 132769719345253) ^ 902648868 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_133201182612481 : Nat.Prime 133201182612481 := by
  apply lucas_primality 133201182612481 (29 : ZMod 133201182612481)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (5, 1), (23, 1), (377041391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (5, 1), (23, 1), (377041391, 1)] : List FactorBlock).map factorBlockValue).prod) = 133201182612481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_377041391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 133201182612481) ^ 66600591306240 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (29 : ZMod 133201182612481) ^ 44400394204160 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (29 : ZMod 133201182612481) ^ 26640236522496 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (29 : ZMod 133201182612481) ^ 5791355765760 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (29 : ZMod 133201182612481) ^ 353280 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_161037068379563 : Nat.Prime 161037068379563 := by
  apply lucas_primality 161037068379563 (2 : ZMod 161037068379563)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (397, 1), (380707, 1), (532739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (397, 1), (380707, 1), (532739, 1)] : List FactorBlock).map factorBlockValue).prod) = 161037068379563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_397
      · exact prime_oneHundredFiftyOneES_380707
      · exact prime_oneHundredFiftyOneES_532739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 161037068379563) ^ 80518534189781 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 161037068379563) ^ 405634932946 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 161037068379563) ^ 422994766 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 161037068379563) ^ 302281358 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_228695566762571 : Nat.Prime 228695566762571 := by
  apply lucas_primality 228695566762571 (2 : ZMod 228695566762571)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (22869556676257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (22869556676257, 1)] : List FactorBlock).map factorBlockValue).prod) = 228695566762571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_22869556676257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 228695566762571) ^ 114347783381285 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 228695566762571) ^ 45739113352514 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 228695566762571) ^ 10 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_233382214117453 : Nat.Prime 233382214117453 := by
  apply lucas_primality 233382214117453 (6 : ZMod 233382214117453)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (443, 1), (43901846147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (443, 1), (43901846147, 1)] : List FactorBlock).map factorBlockValue).prod) = 233382214117453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_443
      · exact prime_oneHundredFiftyOneES_43901846147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 233382214117453) ^ 116691107058726 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 233382214117453) ^ 77794071372484 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 233382214117453) ^ 526822153764 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 233382214117453) ^ 5316 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_372183102560261 : Nat.Prime 372183102560261 := by
  apply lucas_primality 372183102560261 (2 : ZMod 372183102560261)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (307859, 1), (60447007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (307859, 1), (60447007, 1)] : List FactorBlock).map factorBlockValue).prod) = 372183102560261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_307859
      · exact prime_oneHundredFiftyOneES_60447007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 372183102560261) ^ 186091551280130 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 372183102560261) ^ 74436620512052 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 372183102560261) ^ 1208940140 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 372183102560261) ^ 6157180 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_385014967634749 : Nat.Prime 385014967634749 := by
  apply lucas_primality 385014967634749 (6 : ZMod 385014967634749)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (2916780057839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (2916780057839, 1)] : List FactorBlock).map factorBlockValue).prod) = 385014967634749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_2916780057839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 385014967634749) ^ 192507483817374 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 385014967634749) ^ 128338322544916 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 385014967634749) ^ 35001360694068 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 385014967634749) ^ 132 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_436399896584347 : Nat.Prime 436399896584347 := by
  apply lucas_primality 436399896584347 (3 : ZMod 436399896584347)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (701, 1), (103756513691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (701, 1), (103756513691, 1)] : List FactorBlock).map factorBlockValue).prod) = 436399896584347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_701
      · exact prime_oneHundredFiftyOneES_103756513691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 436399896584347) ^ 218199948292173 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 436399896584347) ^ 145466632194782 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 436399896584347) ^ 622539082146 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 436399896584347) ^ 4206 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_586113085360601 : Nat.Prime 586113085360601 := by
  apply lucas_primality 586113085360601 (3 : ZMod 586113085360601)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7, 1), (2381, 1), (175830409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7, 1), (2381, 1), (175830409, 1)] : List FactorBlock).map factorBlockValue).prod) = 586113085360601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_2381
      · exact prime_oneHundredFiftyOneES_175830409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 586113085360601) ^ 293056542680300 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 586113085360601) ^ 117222617072120 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 586113085360601) ^ 83730440765800 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 586113085360601) ^ 246162572600 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 586113085360601) ^ 3333400 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_613475709937907 : Nat.Prime 613475709937907 := by
  apply lucas_primality 613475709937907 (2 : ZMod 613475709937907)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (13336428476911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (13336428476911, 1)] : List FactorBlock).map factorBlockValue).prod) = 613475709937907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_13336428476911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 613475709937907) ^ 306737854968953 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 613475709937907) ^ 26672856953822 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 613475709937907) ^ 46 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_662441219748491 : Nat.Prime 662441219748491 := by
  apply lucas_primality 662441219748491 (6 : ZMod 662441219748491)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (31, 1), (433, 1), (1663, 1), (32611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (31, 1), (433, 1), (1663, 1), (32611, 1)] : List FactorBlock).map factorBlockValue).prod) = 662441219748491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_433
      · exact prime_oneHundredFiftyOneES_1663
      · exact prime_oneHundredFiftyOneES_32611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 662441219748491) ^ 331220609874245 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 662441219748491) ^ 132488243949698 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 662441219748491) ^ 94634459964070 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 662441219748491) ^ 50957016903730 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 662441219748491) ^ 21369071604790 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 662441219748491) ^ 1529887343530 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 662441219748491) ^ 398341082230 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 662441219748491) ^ 20313428590 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_700389041400803 : Nat.Prime 700389041400803 := by
  apply lucas_primality 700389041400803 (5 : ZMod 700389041400803)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (823, 1), (1619, 1), (1064059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (823, 1), (1619, 1), (1064059, 1)] : List FactorBlock).map factorBlockValue).prod) = 700389041400803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_823
      · exact prime_oneHundredFiftyOneES_1619
      · exact prime_oneHundredFiftyOneES_1064059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 700389041400803) ^ 350194520700401 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 700389041400803) ^ 53876080107754 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 700389041400803) ^ 36862581126358 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 700389041400803) ^ 851019491374 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 700389041400803) ^ 432605955158 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 700389041400803) ^ 658223878 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_707629874244649 : Nat.Prime 707629874244649 := by
  apply lucas_primality 707629874244649 (7 : ZMod 707629874244649)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (79, 1), (1973, 1), (2081, 1), (90901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (79, 1), (1973, 1), (2081, 1), (90901, 1)] : List FactorBlock).map factorBlockValue).prod) = 707629874244649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_79
      · exact prime_oneHundredFiftyOneES_1973
      · exact prime_oneHundredFiftyOneES_2081
      · exact prime_oneHundredFiftyOneES_90901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 707629874244649) ^ 353814937122324 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 707629874244649) ^ 235876624748216 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 707629874244649) ^ 8957340180312 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 707629874244649) ^ 358656803976 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 707629874244649) ^ 340043188008 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 707629874244649) ^ 7784621448 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_774469259700287 : Nat.Prime 774469259700287 := by
  apply lucas_primality 774469259700287 (5 : ZMod 774469259700287)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (857, 1), (1427, 1), (1753, 1), (180629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (857, 1), (1427, 1), (1753, 1), (180629, 1)] : List FactorBlock).map factorBlockValue).prod) = 774469259700287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_857
      · exact prime_oneHundredFiftyOneES_1427
      · exact prime_oneHundredFiftyOneES_1753
      · exact prime_oneHundredFiftyOneES_180629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 774469259700287) ^ 387234629850143 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 774469259700287) ^ 903698085998 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 774469259700287) ^ 542725479818 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 774469259700287) ^ 441796497262 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 774469259700287) ^ 4287624134 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_844360239481331 : Nat.Prime 844360239481331 := by
  apply lucas_primality 844360239481331 (2 : ZMod 844360239481331)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (83, 1), (7113996457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (83, 1), (7113996457, 1)] : List FactorBlock).map factorBlockValue).prod) = 844360239481331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_83
      · exact prime_oneHundredFiftyOneES_7113996457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 844360239481331) ^ 422180119740665 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 844360239481331) ^ 168872047896266 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 844360239481331) ^ 76760021771030 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 844360239481331) ^ 64950787652410 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 844360239481331) ^ 10173014933510 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 844360239481331) ^ 118690 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_975465420257833 : Nat.Prime 975465420257833 := by
  apply lucas_primality 975465420257833 (5 : ZMod 975465420257833)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (17, 1), (19, 1), (17976290363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (17, 1), (19, 1), (17976290363, 1)] : List FactorBlock).map factorBlockValue).prod) = 975465420257833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_17976290363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 975465420257833) ^ 487732710128916 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 975465420257833) ^ 325155140085944 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 975465420257833) ^ 139352202893976 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 975465420257833) ^ 57380318838696 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 975465420257833) ^ 51340285276728 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 975465420257833) ^ 54264 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1324882439496983 : Nat.Prime 1324882439496983 := by
  apply lucas_primality 1324882439496983 (5 : ZMod 1324882439496983)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (662441219748491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (662441219748491, 1)] : List FactorBlock).map factorBlockValue).prod) = 1324882439496983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_662441219748491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1324882439496983) ^ 662441219748491 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 1324882439496983) ^ 2 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1381332555959039 : Nat.Prime 1381332555959039 := by
  apply lucas_primality 1381332555959039 (13 : ZMod 1381332555959039)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (389, 1), (3823, 1), (464423677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (389, 1), (3823, 1), (464423677, 1)] : List FactorBlock).map factorBlockValue).prod) = 1381332555959039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_389
      · exact prime_oneHundredFiftyOneES_3823
      · exact prime_oneHundredFiftyOneES_464423677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1381332555959039) ^ 690666277979519 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 1381332555959039) ^ 3550983434342 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 1381332555959039) ^ 361321620706 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 1381332555959039) ^ 2974294 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1745599586337389 : Nat.Prime 1745599586337389 := by
  apply lucas_primality 1745599586337389 (2 : ZMod 1745599586337389)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (436399896584347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (436399896584347, 1)] : List FactorBlock).map factorBlockValue).prod) = 1745599586337389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_436399896584347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1745599586337389) ^ 872799793168694 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1745599586337389) ^ 4 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1796361227939321 : Nat.Prime 1796361227939321 := by
  apply lucas_primality 1796361227939321 (3 : ZMod 1796361227939321)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (19, 1), (157, 1), (1481, 1), (1452203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (19, 1), (157, 1), (1481, 1), (1452203, 1)] : List FactorBlock).map factorBlockValue).prod) = 1796361227939321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_157
      · exact prime_oneHundredFiftyOneES_1481
      · exact prime_oneHundredFiftyOneES_1452203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1796361227939321) ^ 898180613969660 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796361227939321) ^ 359272245587864 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796361227939321) ^ 256623032562760 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796361227939321) ^ 94545327786280 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796361227939321) ^ 11441791260760 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796361227939321) ^ 1212938033720 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1796361227939321) ^ 1236990440 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2114245895214113 : Nat.Prime 2114245895214113 := by
  apply lucas_primality 2114245895214113 (3 : ZMod 2114245895214113)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (6247, 1), (961482373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (6247, 1), (961482373, 1)] : List FactorBlock).map factorBlockValue).prod) = 2114245895214113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_6247
      · exact prime_oneHundredFiftyOneES_961482373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2114245895214113) ^ 1057122947607056 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2114245895214113) ^ 192204172292192 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2114245895214113) ^ 338441795296 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 2114245895214113) ^ 2198944 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2657047731035063 : Nat.Prime 2657047731035063 := by
  apply lucas_primality 2657047731035063 (5 : ZMod 2657047731035063)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (97, 1), (223, 1), (3232504679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (97, 1), (223, 1), (3232504679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2657047731035063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_97
      · exact prime_oneHundredFiftyOneES_223
      · exact prime_oneHundredFiftyOneES_3232504679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2657047731035063) ^ 1328523865517531 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 2657047731035063) ^ 139844617422898 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 2657047731035063) ^ 27392244649846 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 2657047731035063) ^ 11915012246794 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 2657047731035063) ^ 821978 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_3921000148937293 : Nat.Prime 3921000148937293 := by
  apply lucas_primality 3921000148937293 (2 : ZMod 3921000148937293)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2269, 1), (144006175589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2269, 1), (144006175589, 1)] : List FactorBlock).map factorBlockValue).prod) = 3921000148937293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_2269
      · exact prime_oneHundredFiftyOneES_144006175589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3921000148937293) ^ 1960500074468646 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 3921000148937293) ^ 1307000049645764 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 3921000148937293) ^ 1728074107068 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 3921000148937293) ^ 27228 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_6913753737787139 : Nat.Prime 6913753737787139 := by
  apply lucas_primality 6913753737787139 (2 : ZMod 6913753737787139)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2632151, 1), (119393429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2632151, 1), (119393429, 1)] : List FactorBlock).map factorBlockValue).prod) = 6913753737787139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_2632151
      · exact prime_oneHundredFiftyOneES_119393429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6913753737787139) ^ 3456876868893569 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6913753737787139) ^ 628523067071558 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6913753737787139) ^ 2626655438 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6913753737787139) ^ 57907322 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_6945988167117059 : Nat.Prime 6945988167117059 := by
  apply lucas_primality 6945988167117059 (2 : ZMod 6945988167117059)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (199, 1), (405865850597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (199, 1), (405865850597, 1)] : List FactorBlock).map factorBlockValue).prod) = 6945988167117059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_43
      · exact prime_oneHundredFiftyOneES_199
      · exact prime_oneHundredFiftyOneES_405865850597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6945988167117059) ^ 3472994083558529 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6945988167117059) ^ 161534608537606 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6945988167117059) ^ 34904463151342 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6945988167117059) ^ 17114 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_7425912782854589 : Nat.Prime 7425912782854589 := by
  apply lucas_primality 7425912782854589 (2 : ZMod 7425912782854589)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (193, 1), (874459818989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (193, 1), (874459818989, 1)] : List FactorBlock).map factorBlockValue).prod) = 7425912782854589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_193
      · exact prime_oneHundredFiftyOneES_874459818989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7425912782854589) ^ 3712956391427294 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7425912782854589) ^ 675082980259508 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7425912782854589) ^ 38476232035516 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7425912782854589) ^ 8492 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_7440477192039179 : Nat.Prime 7440477192039179 := by
  apply lucas_primality 7440477192039179 (2 : ZMod 7440477192039179)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (3813353, 1), (19909837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (3813353, 1), (19909837, 1)] : List FactorBlock).map factorBlockValue).prod) = 7440477192039179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_3813353
      · exact prime_oneHundredFiftyOneES_19909837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7440477192039179) ^ 3720238596019589 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7440477192039179) ^ 1062925313148454 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7440477192039179) ^ 1951164026 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7440477192039179) ^ 373708594 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_12840189618724379 : Nat.Prime 12840189618724379 := by
  apply lucas_primality 12840189618724379 (2 : ZMod 12840189618724379)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6029, 1), (1064868935041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6029, 1), (1064868935041, 1)] : List FactorBlock).map factorBlockValue).prod) = 12840189618724379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_6029
      · exact prime_oneHundredFiftyOneES_1064868935041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12840189618724379) ^ 6420094809362189 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 12840189618724379) ^ 2129737870082 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 12840189618724379) ^ 12058 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_14880954384078359 : Nat.Prime 14880954384078359 := by
  apply lucas_primality 14880954384078359 (11 : ZMod 14880954384078359)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7440477192039179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7440477192039179, 1)] : List FactorBlock).map factorBlockValue).prod) = 14880954384078359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7440477192039179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 14880954384078359) ^ 7440477192039179 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 14880954384078359) ^ 2 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_15647674741522121 : Nat.Prime 15647674741522121 := by
  apply lucas_primality 15647674741522121 (3 : ZMod 15647674741522121)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (35562897139823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (35562897139823, 1)] : List FactorBlock).map factorBlockValue).prod) = 15647674741522121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_35562897139823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15647674741522121) ^ 7823837370761060 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 15647674741522121) ^ 3129534948304424 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 15647674741522121) ^ 1422515885592920 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 15647674741522121) ^ 440 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_15950368458385583 : Nat.Prime 15950368458385583 := by
  apply lucas_primality 15950368458385583 (10 : ZMod 15950368458385583)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (613475709937907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (613475709937907, 1)] : List FactorBlock).map factorBlockValue).prod) = 15950368458385583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_613475709937907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 15950368458385583) ^ 7975184229192791 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 15950368458385583) ^ 1226951419875814 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 15950368458385583) ^ 26 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_18500599983420937 : Nat.Prime 18500599983420937 := by
  apply lucas_primality 18500599983420937 (10 : ZMod 18500599983420937)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (41, 1), (61, 1), (17471, 1), (1960201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (41, 1), (61, 1), (17471, 1), (1960201, 1)] : List FactorBlock).map factorBlockValue).prod) = 18500599983420937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_41
      · exact prime_oneHundredFiftyOneES_61
      · exact prime_oneHundredFiftyOneES_17471
      · exact prime_oneHundredFiftyOneES_1960201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 18500599983420937) ^ 9250299991710468 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 18500599983420937) ^ 6166866661140312 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 18500599983420937) ^ 451234145937096 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 18500599983420937) ^ 303288524318376 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 18500599983420937) ^ 1058931943416 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 18500599983420937) ^ 9438113736 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_19535006918803639 : Nat.Prime 19535006918803639 := by
  apply lucas_primality 19535006918803639 (3 : ZMod 19535006918803639)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (23, 1), (197, 1), (37819401857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (23, 1), (197, 1), (37819401857, 1)] : List FactorBlock).map factorBlockValue).prod) = 19535006918803639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_197
      · exact prime_oneHundredFiftyOneES_37819401857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19535006918803639) ^ 9767503459401819 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 19535006918803639) ^ 6511668972934546 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 19535006918803639) ^ 1028158258884402 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 19535006918803639) ^ 849348126904506 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 19535006918803639) ^ 99162471669054 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 19535006918803639) ^ 516534 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_25023043645499377 : Nat.Prime 25023043645499377 := by
  apply lucas_primality 25023043645499377 (5 : ZMod 25023043645499377)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (6263, 1), (41381, 1), (670493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (6263, 1), (41381, 1), (670493, 1)] : List FactorBlock).map factorBlockValue).prod) = 25023043645499377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_6263
      · exact prime_oneHundredFiftyOneES_41381
      · exact prime_oneHundredFiftyOneES_670493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25023043645499377) ^ 12511521822749688 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 25023043645499377) ^ 8341014548499792 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 25023043645499377) ^ 3995376599952 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 25023043645499377) ^ 604698862896 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 25023043645499377) ^ 37320365232 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_35028328659639349 : Nat.Prime 35028328659639349 := by
  apply lucas_primality 35028328659639349 (6 : ZMod 35028328659639349)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (131, 1), (2025695619919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (131, 1), (2025695619919, 1)] : List FactorBlock).map factorBlockValue).prod) = 35028328659639349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_131
      · exact prime_oneHundredFiftyOneES_2025695619919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 35028328659639349) ^ 17514164329819674 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 35028328659639349) ^ 11676109553213116 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 35028328659639349) ^ 3184393514512668 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 35028328659639349) ^ 267391821829308 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 35028328659639349) ^ 17292 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_36000598298957741 : Nat.Prime 36000598298957741 := by
  apply lucas_primality 36000598298957741 (2 : ZMod 36000598298957741)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (1553, 1), (165580895497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (1553, 1), (165580895497, 1)] : List FactorBlock).map factorBlockValue).prod) = 36000598298957741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_1553
      · exact prime_oneHundredFiftyOneES_165580895497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36000598298957741) ^ 18000299149478870 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 36000598298957741) ^ 7200119659791548 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 36000598298957741) ^ 5142942614136820 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 36000598298957741) ^ 23181325369580 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 36000598298957741) ^ 217420 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_43954832492729671 : Nat.Prime 43954832492729671 := by
  apply lucas_primality 43954832492729671 (7 : ZMod 43954832492729671)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1307, 1), (1121010775127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1307, 1), (1121010775127, 1)] : List FactorBlock).map factorBlockValue).prod) = 43954832492729671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_1307
      · exact prime_oneHundredFiftyOneES_1121010775127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 43954832492729671) ^ 21977416246364835 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 43954832492729671) ^ 14651610830909890 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 43954832492729671) ^ 8790966498545934 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 43954832492729671) ^ 33630323253810 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 43954832492729671) ^ 39210 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_49646475480224897 : Nat.Prime 49646475480224897 := by
  apply lucas_primality 49646475480224897 (3 : ZMod 49646475480224897)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (13, 1), (953, 1), (4472436259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (13, 1), (953, 1), (4472436259, 1)] : List FactorBlock).map factorBlockValue).prod) = 49646475480224897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_953
      · exact prime_oneHundredFiftyOneES_4472436259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49646475480224897) ^ 24823237740112448 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 49646475480224897) ^ 7092353640032128 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 49646475480224897) ^ 3818959652324992 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 49646475480224897) ^ 52094937544832 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 49646475480224897) ^ 11100544 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_72231166965295171 : Nat.Prime 72231166965295171 := by
  apply lucas_primality 72231166965295171 (2 : ZMod 72231166965295171)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 3), (6379, 1), (366805129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 3), (6379, 1), (366805129, 1)] : List FactorBlock).map factorBlockValue).prod) = 72231166965295171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_6379
      · exact prime_oneHundredFiftyOneES_366805129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 72231166965295171) ^ 36115583482647585 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 72231166965295171) ^ 24077055655098390 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 72231166965295171) ^ 14446233393059034 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 72231166965295171) ^ 10318738137899310 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 72231166965295171) ^ 11323274332230 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 72231166965295171) ^ 196919730 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_78158451537654811 : Nat.Prime 78158451537654811 := by
  apply lucas_primality 78158451537654811 (2 : ZMod 78158451537654811)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (372183102560261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (372183102560261, 1)] : List FactorBlock).map factorBlockValue).prod) = 78158451537654811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_372183102560261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78158451537654811) ^ 39079225768827405 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 78158451537654811) ^ 26052817179218270 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 78158451537654811) ^ 15631690307530962 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 78158451537654811) ^ 11165493076807830 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 78158451537654811) ^ 210 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_84732739892975197 : Nat.Prime 84732739892975197 := by
  apply lucas_primality 84732739892975197 (2 : ZMod 84732739892975197)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (71323855128767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (71323855128767, 1)] : List FactorBlock).map factorBlockValue).prod) = 84732739892975197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_71323855128767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84732739892975197) ^ 42366369946487598 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 84732739892975197) ^ 28244246630991732 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 84732739892975197) ^ 7702976353906836 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 84732739892975197) ^ 1188 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_100092174581997509 : Nat.Prime 100092174581997509 := by
  apply lucas_primality 100092174581997509 (2 : ZMod 100092174581997509)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (25023043645499377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (25023043645499377, 1)] : List FactorBlock).map factorBlockValue).prod) = 100092174581997509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_25023043645499377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 100092174581997509) ^ 50046087290998754 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 100092174581997509) ^ 4 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_100804277649264187 : Nat.Prime 100804277649264187 := by
  apply lucas_primality 100804277649264187 (2 : ZMod 100804277649264187)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (359, 1), (2463086489011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (359, 1), (2463086489011, 1)] : List FactorBlock).map factorBlockValue).prod) = 100804277649264187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_359
      · exact prime_oneHundredFiftyOneES_2463086489011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 100804277649264187) ^ 50402138824632093 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 100804277649264187) ^ 33601425883088062 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 100804277649264187) ^ 5305488297329694 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 100804277649264187) ^ 280791859747254 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 100804277649264187) ^ 40926 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_255098922259990043 : Nat.Prime 255098922259990043 := by
  apply lucas_primality 255098922259990043 (2 : ZMod 255098922259990043)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (563, 1), (17427170532859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (563, 1), (17427170532859, 1)] : List FactorBlock).map factorBlockValue).prod) = 255098922259990043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_563
      · exact prime_oneHundredFiftyOneES_17427170532859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 255098922259990043) ^ 127549461129995021 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 255098922259990043) ^ 19622994019999234 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 255098922259990043) ^ 453106433854334 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 255098922259990043) ^ 14638 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_308679900701260499 : Nat.Prime 308679900701260499 := by
  apply lucas_primality 308679900701260499 (2 : ZMod 308679900701260499)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (2114245895214113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (2114245895214113, 1)] : List FactorBlock).map factorBlockValue).prod) = 308679900701260499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_73
      · exact prime_oneHundredFiftyOneES_2114245895214113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 308679900701260499) ^ 154339950350630249 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 308679900701260499) ^ 4228491790428226 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 308679900701260499) ^ 146 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_468228165087501737 : Nat.Prime 468228165087501737 := by
  apply lucas_primality 468228165087501737 (3 : ZMod 468228165087501737)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1976453, 1), (29612907889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1976453, 1), (29612907889, 1)] : List FactorBlock).map factorBlockValue).prod) = 468228165087501737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_1976453
      · exact prime_oneHundredFiftyOneES_29612907889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 468228165087501737) ^ 234114082543750868 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 468228165087501737) ^ 236903263112 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 468228165087501737) ^ 15811624 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_471061539634278881 : Nat.Prime 471061539634278881 := by
  apply lucas_primality 471061539634278881 (11 : ZMod 471061539634278881)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (1216421, 1), (345760769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (1216421, 1), (345760769, 1)] : List FactorBlock).map factorBlockValue).prod) = 471061539634278881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_1216421
      · exact prime_oneHundredFiftyOneES_345760769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 471061539634278881) ^ 235530769817139440 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 471061539634278881) ^ 94212307926855776 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 471061539634278881) ^ 67294505662039840 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 471061539634278881) ^ 387252061280 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 471061539634278881) ^ 1362391520 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_620384794267342009 : Nat.Prime 620384794267342009 := by
  apply lucas_primality 620384794267342009 (14 : ZMod 620384794267342009)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (160507, 1), (339091, 1), (474941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (160507, 1), (339091, 1), (474941, 1)] : List FactorBlock).map factorBlockValue).prod) = 620384794267342009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_160507
      · exact prime_oneHundredFiftyOneES_339091
      · exact prime_oneHundredFiftyOneES_474941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 620384794267342009) ^ 310192397133671004 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (14 : ZMod 620384794267342009) ^ 206794931422447336 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (14 : ZMod 620384794267342009) ^ 3865157247144 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (14 : ZMod 620384794267342009) ^ 1829552522088 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (14 : ZMod 620384794267342009) ^ 1306235499288 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_984995528105272279 : Nat.Prime 984995528105272279 := by
  apply lucas_primality 984995528105272279 (6 : ZMod 984995528105272279)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (23, 1), (89, 1), (127, 1), (64187, 1), (200779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (23, 1), (89, 1), (127, 1), (64187, 1), (200779, 1)] : List FactorBlock).map factorBlockValue).prod) = 984995528105272279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_89
      · exact prime_oneHundredFiftyOneES_127
      · exact prime_oneHundredFiftyOneES_64187
      · exact prime_oneHundredFiftyOneES_200779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 984995528105272279) ^ 492497764052636139 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 984995528105272279) ^ 328331842701757426 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 984995528105272279) ^ 140713646872181754 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 984995528105272279) ^ 42825892526316186 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 984995528105272279) ^ 11067365484328902 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 984995528105272279) ^ 7755870300041514 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 984995528105272279) ^ 15345716860194 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 984995528105272279) ^ 4905869279682 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1063302200814882359 : Nat.Prime 1063302200814882359 := by
  apply lucas_primality 1063302200814882359 (7 : ZMod 1063302200814882359)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (1123, 1), (1447, 1), (1749592157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (1123, 1), (1447, 1), (1749592157, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063302200814882359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_1123
      · exact prime_oneHundredFiftyOneES_1447
      · exact prime_oneHundredFiftyOneES_1749592157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1063302200814882359) ^ 531651100407441179 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 1063302200814882359) ^ 96663836437716578 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 1063302200814882359) ^ 62547188283228374 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 1063302200814882359) ^ 946840784340946 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 1063302200814882359) ^ 734832205124314 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 1063302200814882359) ^ 607742894 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1235757968250593989 : Nat.Prime 1235757968250593989 := by
  apply lucas_primality 1235757968250593989 (2 : ZMod 1235757968250593989)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (503453, 1), (204547059383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (503453, 1), (204547059383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1235757968250593989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_503453
      · exact prime_oneHundredFiftyOneES_204547059383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1235757968250593989) ^ 617878984125296994 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1235757968250593989) ^ 411919322750197996 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1235757968250593989) ^ 2454564712596 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1235757968250593989) ^ 6041436 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1506371152488201997 : Nat.Prime 1506371152488201997 := by
  apply lucas_primality 1506371152488201997 (2 : ZMod 1506371152488201997)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (47, 1), (5082551, 1), (22847743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (47, 1), (5082551, 1), (22847743, 1)] : List FactorBlock).map factorBlockValue).prod) = 1506371152488201997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_47
      · exact prime_oneHundredFiftyOneES_5082551
      · exact prime_oneHundredFiftyOneES_22847743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1506371152488201997) ^ 753185576244100998 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506371152488201997) ^ 502123717496067332 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506371152488201997) ^ 65494397934269652 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506371152488201997) ^ 32050450052940468 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506371152488201997) ^ 296380922196 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1506371152488201997) ^ 65930851572 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1868788344955895257 : Nat.Prime 1868788344955895257 := by
  apply lucas_primality 1868788344955895257 (5 : ZMod 1868788344955895257)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (47309, 1), (44483953993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (47309, 1), (44483953993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1868788344955895257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_37
      · exact prime_oneHundredFiftyOneES_47309
      · exact prime_oneHundredFiftyOneES_44483953993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1868788344955895257) ^ 934394172477947628 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 1868788344955895257) ^ 622929448318631752 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 1868788344955895257) ^ 50507793106916088 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 1868788344955895257) ^ 39501751145784 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 1868788344955895257) ^ 42010392 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1992570705717971179 : Nat.Prime 1992570705717971179 := by
  apply lucas_primality 1992570705717971179 (2 : ZMod 1992570705717971179)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19535006918803639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19535006918803639, 1)] : List FactorBlock).map factorBlockValue).prod) = 1992570705717971179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_19535006918803639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1992570705717971179) ^ 996285352858985589 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1992570705717971179) ^ 664190235239323726 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1992570705717971179) ^ 117210041512821834 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1992570705717971179) ^ 102 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_6117856753595055893 : Nat.Prime 6117856753595055893 := by
  apply lucas_primality 6117856753595055893 (2 : ZMod 6117856753595055893)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257, 1), (3187, 1), (1867343119847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257, 1), (3187, 1), (1867343119847, 1)] : List FactorBlock).map factorBlockValue).prod) = 6117856753595055893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_257
      · exact prime_oneHundredFiftyOneES_3187
      · exact prime_oneHundredFiftyOneES_1867343119847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6117856753595055893) ^ 3058928376797527946 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117856753595055893) ^ 23804890091809556 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117856753595055893) ^ 1919628727202716 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117856753595055893) ^ 3276236 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_9674538883326363391 : Nat.Prime 9674538883326363391 := by
  apply lucas_primality 9674538883326363391 (3 : ZMod 9674538883326363391)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (15161, 1), (15647, 1), (1359408839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (15161, 1), (15647, 1), (1359408839, 1)] : List FactorBlock).map factorBlockValue).prod) = 9674538883326363391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_15161
      · exact prime_oneHundredFiftyOneES_15647
      · exact prime_oneHundredFiftyOneES_1359408839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9674538883326363391) ^ 4837269441663181695 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 9674538883326363391) ^ 3224846294442121130 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 9674538883326363391) ^ 1934907776665272678 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 9674538883326363391) ^ 638120103114990 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 9674538883326363391) ^ 618299922242370 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 9674538883326363391) ^ 7116725010 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_14406692752208753239 : Nat.Prime 14406692752208753239 := by
  apply lucas_primality 14406692752208753239 (3 : ZMod 14406692752208753239)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (12840189618724379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (12840189618724379, 1)] : List FactorBlock).map factorBlockValue).prod) = 14406692752208753239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_12840189618724379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14406692752208753239) ^ 7203346376104376619 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 14406692752208753239) ^ 4802230917402917746 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 14406692752208753239) ^ 1309699341109886658 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 14406692752208753239) ^ 847452514835809014 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 14406692752208753239) ^ 1122 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_32325143473610181619 : Nat.Prime 32325143473610181619 := by
  apply lucas_primality 32325143473610181619 (2 : ZMod 32325143473610181619)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 1), (547, 1), (71892124424777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 1), (547, 1), (71892124424777, 1)] : List FactorBlock).map factorBlockValue).prod) = 32325143473610181619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_137
      · exact prime_oneHundredFiftyOneES_547
      · exact prime_oneHundredFiftyOneES_71892124424777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32325143473610181619) ^ 16162571736805090809 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 32325143473610181619) ^ 10775047824536727206 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 32325143473610181619) ^ 235949952362118114 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 32325143473610181619) ^ 59095326277166694 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 32325143473610181619) ^ 449634 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_36152907659716847929 : Nat.Prime 36152907659716847929 := by
  apply lucas_primality 36152907659716847929 (7 : ZMod 36152907659716847929)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1506371152488201997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1506371152488201997, 1)] : List FactorBlock).map factorBlockValue).prod) = 36152907659716847929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_1506371152488201997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 36152907659716847929) ^ 18076453829858423964 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 36152907659716847929) ^ 12050969219905615976 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 36152907659716847929) ^ 24 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_42920747567267744821 : Nat.Prime 42920747567267744821 := by
  apply lucas_primality 42920747567267744821 (6 : ZMod 42920747567267744821)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (37, 1), (11689, 1), (1654005481679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (37, 1), (11689, 1), (1654005481679, 1)] : List FactorBlock).map factorBlockValue).prod) = 42920747567267744821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_37
      · exact prime_oneHundredFiftyOneES_11689
      · exact prime_oneHundredFiftyOneES_1654005481679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 42920747567267744821) ^ 21460373783633872410 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 42920747567267744821) ^ 14306915855755914940 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 42920747567267744821) ^ 8584149513453548964 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 42920747567267744821) ^ 1160020204520749860 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 42920747567267744821) ^ 3671892169327380 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 42920747567267744821) ^ 25949580 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_44113206215350451717 : Nat.Prime 44113206215350451717 := by
  apply lucas_primality 44113206215350451717 (2 : ZMod 44113206215350451717)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (68483, 1), (161037068379563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (68483, 1), (161037068379563, 1)] : List FactorBlock).map factorBlockValue).prod) = 44113206215350451717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_68483
      · exact prime_oneHundredFiftyOneES_161037068379563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44113206215350451717) ^ 22056603107675225858 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 44113206215350451717) ^ 644148273518252 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 44113206215350451717) ^ 273932 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_63454617720594891163 : Nat.Prime 63454617720594891163 := by
  apply lucas_primality 63454617720594891163 (2 : ZMod 63454617720594891163)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1685936969, 1), (2090977661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1685936969, 1), (2090977661, 1)] : List FactorBlock).map factorBlockValue).prod) = 63454617720594891163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_1685936969
      · exact prime_oneHundredFiftyOneES_2090977661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 63454617720594891163) ^ 31727308860297445581 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 63454617720594891163) ^ 21151539240198297054 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 63454617720594891163) ^ 37637597898 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 63454617720594891163) ^ 30346865442 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_68186276125114174277 : Nat.Prime 68186276125114174277 := by
  apply lucas_primality 68186276125114174277 (2 : ZMod 68186276125114174277)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5987, 1), (32561, 1), (87443994667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5987, 1), (32561, 1), (87443994667, 1)] : List FactorBlock).map factorBlockValue).prod) = 68186276125114174277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5987
      · exact prime_oneHundredFiftyOneES_32561
      · exact prime_oneHundredFiftyOneES_87443994667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68186276125114174277) ^ 34093138062557087138 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 68186276125114174277) ^ 11389055641408748 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 68186276125114174277) ^ 2094108784285316 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 68186276125114174277) ^ 779770828 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_72406751566458516629 : Nat.Prime 72406751566458516629 := by
  apply lucas_primality 72406751566458516629 (2 : ZMod 72406751566458516629)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6037, 1), (249433, 1), (12021093817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6037, 1), (249433, 1), (12021093817, 1)] : List FactorBlock).map factorBlockValue).prod) = 72406751566458516629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_6037
      · exact prime_oneHundredFiftyOneES_249433
      · exact prime_oneHundredFiftyOneES_12021093817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72406751566458516629) ^ 36203375783229258314 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 72406751566458516629) ^ 11993829976223044 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 72406751566458516629) ^ 290285373492916 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 72406751566458516629) ^ 6023308084 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_101321149302075680801 : Nat.Prime 101321149302075680801 := by
  apply lucas_primality 101321149302075680801 (3 : ZMod 101321149302075680801)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (4981747, 1), (25423096883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (4981747, 1), (25423096883, 1)] : List FactorBlock).map factorBlockValue).prod) = 101321149302075680801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_4981747
      · exact prime_oneHundredFiftyOneES_25423096883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101321149302075680801) ^ 50660574651037840400 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 101321149302075680801) ^ 20264229860415136160 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 101321149302075680801) ^ 20338477506400 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 101321149302075680801) ^ 3985397600 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_241804380288611924521 : Nat.Prime 241804380288611924521 := by
  apply lucas_primality 241804380288611924521 (7 : ZMod 241804380288611924521)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (3793, 1), (48295580432977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (3793, 1), (48295580432977, 1)] : List FactorBlock).map factorBlockValue).prod) = 241804380288611924521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_3793
      · exact prime_oneHundredFiftyOneES_48295580432977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 241804380288611924521) ^ 120902190144305962260 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 241804380288611924521) ^ 80601460096203974840 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 241804380288611924521) ^ 48360876057722384904 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 241804380288611924521) ^ 21982216389873811320 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 241804380288611924521) ^ 63750166171529640 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 241804380288611924521) ^ 5006760 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_438362578281810567829 : Nat.Prime 438362578281810567829 := by
  apply lucas_primality 438362578281810567829 (2 : ZMod 438362578281810567829)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (14321, 1), (29429, 1), (86676901291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (14321, 1), (29429, 1), (86676901291, 1)] : List FactorBlock).map factorBlockValue).prod) = 438362578281810567829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_14321
      · exact prime_oneHundredFiftyOneES_29429
      · exact prime_oneHundredFiftyOneES_86676901291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 438362578281810567829) ^ 219181289140905283914 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 438362578281810567829) ^ 146120859427270189276 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 438362578281810567829) ^ 30609774337114068 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 438362578281810567829) ^ 14895598840660932 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 438362578281810567829) ^ 5057432508 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_546274118687019915221 : Nat.Prime 546274118687019915221 := by
  apply lucas_primality 546274118687019915221 (2 : ZMod 546274118687019915221)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (31, 1), (71, 1), (1061, 1), (14387, 1), (116138689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (31, 1), (71, 1), (1061, 1), (14387, 1), (116138689, 1)] : List FactorBlock).map factorBlockValue).prod) = 546274118687019915221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_71
      · exact prime_oneHundredFiftyOneES_1061
      · exact prime_oneHundredFiftyOneES_14387
      · exact prime_oneHundredFiftyOneES_116138689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 546274118687019915221) ^ 273137059343509957610 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 546274118687019915221) ^ 109254823737403983044 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 546274118687019915221) ^ 78039159812431416460 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 546274118687019915221) ^ 17621745764097416620 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 546274118687019915221) ^ 7694001671648167820 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 546274118687019915221) ^ 514867218366654020 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 546274118687019915221) ^ 37969981141796060 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 546274118687019915221) ^ 4703636000980 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_577629295402566797749 : Nat.Prime 577629295402566797749 := by
  apply lucas_primality 577629295402566797749 (2 : ZMod 577629295402566797749)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (677639, 1), (4324157, 1), (5475791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (677639, 1), (4324157, 1), (5475791, 1)] : List FactorBlock).map factorBlockValue).prod) = 577629295402566797749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_677639
      · exact prime_oneHundredFiftyOneES_4324157
      · exact prime_oneHundredFiftyOneES_5475791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 577629295402566797749) ^ 288814647701283398874 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 577629295402566797749) ^ 192543098467522265916 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 577629295402566797749) ^ 852414479394732 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 577629295402566797749) ^ 133581943348164 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 577629295402566797749) ^ 105487827311628 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_611111159604316531273 : Nat.Prime 611111159604316531273 := by
  apply lucas_primality 611111159604316531273 (10 : ZMod 611111159604316531273)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (59, 1), (313, 1), (397, 1), (1021, 1), (485957551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (59, 1), (313, 1), (397, 1), (1021, 1), (485957551, 1)] : List FactorBlock).map factorBlockValue).prod) = 611111159604316531273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_59
      · exact prime_oneHundredFiftyOneES_313
      · exact prime_oneHundredFiftyOneES_397
      · exact prime_oneHundredFiftyOneES_1021
      · exact prime_oneHundredFiftyOneES_485957551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 611111159604316531273) ^ 305555579802158265636 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 611111159604316531273) ^ 203703719868105510424 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 611111159604316531273) ^ 87301594229188075896 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 611111159604316531273) ^ 10357816264479941208 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 611111159604316531273) ^ 1952431819822097544 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 611111159604316531273) ^ 1539322820162006376 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 611111159604316531273) ^ 598541782178566632 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 611111159604316531273) ^ 1257540207672 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_775803443366644358857 : Nat.Prime 775803443366644358857 := by
  apply lucas_primality 775803443366644358857 (5 : ZMod 775803443366644358857)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (32325143473610181619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (32325143473610181619, 1)] : List FactorBlock).map factorBlockValue).prod) = 775803443366644358857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_32325143473610181619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 775803443366644358857) ^ 387901721683322179428 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 775803443366644358857) ^ 258601147788881452952 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 775803443366644358857) ^ 24 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1045653911062951359241 : Nat.Prime 1045653911062951359241 := by
  apply lucas_primality 1045653911062951359241 (11 : ZMod 1045653911062951359241)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (157, 1), (18500599983420937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (157, 1), (18500599983420937, 1)] : List FactorBlock).map factorBlockValue).prod) = 1045653911062951359241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_157
      · exact prime_oneHundredFiftyOneES_18500599983420937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1045653911062951359241) ^ 522826955531475679620 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 1045653911062951359241) ^ 348551303687650453080 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 1045653911062951359241) ^ 209130782212590271848 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 1045653911062951359241) ^ 6660215994031537320 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (11 : ZMod 1045653911062951359241) ^ 56520 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1246540841349250566803 : Nat.Prime 1246540841349250566803 := by
  apply lucas_primality 1246540841349250566803 (2 : ZMod 1246540841349250566803)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (3877, 1), (3921000148937293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (3877, 1), (3921000148937293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1246540841349250566803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_41
      · exact prime_oneHundredFiftyOneES_3877
      · exact prime_oneHundredFiftyOneES_3921000148937293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1246540841349250566803) ^ 623270420674625283401 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246540841349250566803) ^ 30403435154859769922 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246540841349250566803) ^ 321522012212858026 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1246540841349250566803) ^ 317914 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_4115380189299199259827 : Nat.Prime 4115380189299199259827 := by
  apply lucas_primality 4115380189299199259827 (5 : ZMod 4115380189299199259827)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (179, 1), (14102981, 1), (15982541437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (179, 1), (14102981, 1), (15982541437, 1)] : List FactorBlock).map factorBlockValue).prod) = 4115380189299199259827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_179
      · exact prime_oneHundredFiftyOneES_14102981
      · exact prime_oneHundredFiftyOneES_15982541437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4115380189299199259827) ^ 2057690094649599629913 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 4115380189299199259827) ^ 1371793396433066419942 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 4115380189299199259827) ^ 242081187605835250578 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 4115380189299199259827) ^ 22990950778207817094 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 4115380189299199259827) ^ 291809241556746 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 4115380189299199259827) ^ 257492227098 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_6745446900864752227579 : Nat.Prime 6745446900864752227579 := by
  apply lucas_primality 6745446900864752227579 (2 : ZMod 6745446900864752227579)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (292866391, 1), (31209357691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (292866391, 1), (31209357691, 1)] : List FactorBlock).map factorBlockValue).prod) = 6745446900864752227579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_41
      · exact prime_oneHundredFiftyOneES_292866391
      · exact prime_oneHundredFiftyOneES_31209357691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6745446900864752227579) ^ 3372723450432376113789 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6745446900864752227579) ^ 2248482300288250742526 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6745446900864752227579) ^ 164523095143042737258 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6745446900864752227579) ^ 23032505975958 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 6745446900864752227579) ^ 216135396558 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_9418748486436648576533 : Nat.Prime 9418748486436648576533 := by
  apply lucas_primality 9418748486436648576533 (2 : ZMod 9418748486436648576533)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (47, 1), (71, 1), (100804277649264187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (47, 1), (71, 1), (100804277649264187, 1)] : List FactorBlock).map factorBlockValue).prod) = 9418748486436648576533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_47
      · exact prime_oneHundredFiftyOneES_71
      · exact prime_oneHundredFiftyOneES_100804277649264187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9418748486436648576533) ^ 4709374243218324288266 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 9418748486436648576533) ^ 1345535498062378368076 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 9418748486436648576533) ^ 200398903966737203756 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 9418748486436648576533) ^ 132658429386431670092 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 9418748486436648576533) ^ 93436 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_14666667830503596750553 : Nat.Prime 14666667830503596750553 := by
  apply lucas_primality 14666667830503596750553 (10 : ZMod 14666667830503596750553)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (611111159604316531273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (611111159604316531273, 1)] : List FactorBlock).map factorBlockValue).prod) = 14666667830503596750553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_611111159604316531273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 14666667830503596750553) ^ 7333333915251798375276 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 14666667830503596750553) ^ 4888889276834532250184 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 14666667830503596750553) ^ 24 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_18837496972873297153067 : Nat.Prime 18837496972873297153067 := by
  apply lucas_primality 18837496972873297153067 (2 : ZMod 18837496972873297153067)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9418748486436648576533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9418748486436648576533, 1)] : List FactorBlock).map factorBlockValue).prod) = 18837496972873297153067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_9418748486436648576533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 18837496972873297153067) ^ 9418748486436648576533 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 18837496972873297153067) ^ 2 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_25631990054526314886667 : Nat.Prime 25631990054526314886667 := by
  apply lucas_primality 25631990054526314886667 (2 : ZMod 25631990054526314886667)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (72406751566458516629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (72406751566458516629, 1)] : List FactorBlock).map factorBlockValue).prod) = 25631990054526314886667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_59
      · exact prime_oneHundredFiftyOneES_72406751566458516629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25631990054526314886667) ^ 12815995027263157443333 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 25631990054526314886667) ^ 8543996684842104962222 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 25631990054526314886667) ^ 434440509398751099774 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 25631990054526314886667) ^ 354 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_28015758975226206693473 : Nat.Prime 28015758975226206693473 := by
  apply lucas_primality 28015758975226206693473 (3 : ZMod 28015758975226206693473)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (411311, 1), (1578701, 1), (1348286561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (411311, 1), (1578701, 1), (1348286561, 1)] : List FactorBlock).map factorBlockValue).prod) = 28015758975226206693473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_411311
      · exact prime_oneHundredFiftyOneES_1578701
      · exact prime_oneHundredFiftyOneES_1348286561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28015758975226206693473) ^ 14007879487613103346736 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 28015758975226206693473) ^ 68113322948392352 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 28015758975226206693473) ^ 17746082998127072 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 28015758975226206693473) ^ 20778786784352 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_34355603921000484681473 : Nat.Prime 34355603921000484681473 := by
  apply lucas_primality 34355603921000484681473 (3 : ZMod 34355603921000484681473)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (17, 1), (19373, 1), (3549047, 1), (114815381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (17, 1), (19373, 1), (3549047, 1), (114815381, 1)] : List FactorBlock).map factorBlockValue).prod) = 34355603921000484681473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_19373
      · exact prime_oneHundredFiftyOneES_3549047
      · exact prime_oneHundredFiftyOneES_114815381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34355603921000484681473) ^ 17177801960500242340736 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 34355603921000484681473) ^ 2020917877705910863616 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 34355603921000484681473) ^ 1773375518556779264 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 34355603921000484681473) ^ 9680233572843776 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 34355603921000484681473) ^ 299224752134912 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_36113831852249597852257 : Nat.Prime 36113831852249597852257 := by
  apply lucas_primality 36113831852249597852257 (5 : ZMod 36113831852249597852257)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (29, 1), (829, 1), (15647674741522121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (29, 1), (829, 1), (15647674741522121, 1)] : List FactorBlock).map factorBlockValue).prod) = 36113831852249597852257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_829
      · exact prime_oneHundredFiftyOneES_15647674741522121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36113831852249597852257) ^ 18056915926124798926128 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 36113831852249597852257) ^ 12037943950749865950752 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 36113831852249597852257) ^ 1245304546629296477664 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 36113831852249597852257) ^ 43563126480397584864 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 36113831852249597852257) ^ 2307936 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_44996599715265372813707 : Nat.Prime 44996599715265372813707 := by
  apply lucas_primality 44996599715265372813707 (5 : ZMod 44996599715265372813707)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (775803443366644358857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (775803443366644358857, 1)] : List FactorBlock).map factorBlockValue).prod) = 44996599715265372813707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_29
      · exact prime_oneHundredFiftyOneES_775803443366644358857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 44996599715265372813707) ^ 22498299857632686406853 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 44996599715265372813707) ^ 1551606886733288717714 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 44996599715265372813707) ^ 58 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_216682991113497587113543 : Nat.Prime 216682991113497587113543 := by
  apply lucas_primality 216682991113497587113543 (3 : ZMod 216682991113497587113543)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (36113831852249597852257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (36113831852249597852257, 1)] : List FactorBlock).map factorBlockValue).prod) = 216682991113497587113543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_36113831852249597852257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 216682991113497587113543) ^ 108341495556748793556771 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 216682991113497587113543) ^ 72227663704499195704514 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 216682991113497587113543) ^ 6 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_229345194629401575737687 : Nat.Prime 229345194629401575737687 := by
  apply lucas_primality 229345194629401575737687 (5 : ZMod 229345194629401575737687)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (6745446900864752227579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (6745446900864752227579, 1)] : List FactorBlock).map factorBlockValue).prod) = 229345194629401575737687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_6745446900864752227579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 229345194629401575737687) ^ 114672597314700787868843 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 229345194629401575737687) ^ 13490893801729504455158 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 229345194629401575737687) ^ 34 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_461101337929632550861301 : Nat.Prime 461101337929632550861301 := by
  apply lucas_primality 461101337929632550861301 (2 : ZMod 461101337929632550861301)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (20947, 1), (17625319, 1), (12489284641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (20947, 1), (17625319, 1), (12489284641, 1)] : List FactorBlock).map factorBlockValue).prod) = 461101337929632550861301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_20947
      · exact prime_oneHundredFiftyOneES_17625319
      · exact prime_oneHundredFiftyOneES_12489284641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 461101337929632550861301) ^ 230550668964816275430650 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 461101337929632550861301) ^ 92220267585926510172260 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 461101337929632550861301) ^ 22012762587942547900 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 461101337929632550861301) ^ 26161304537502700 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 461101337929632550861301) ^ 36919755709300 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_486039475903964569981529 : Nat.Prime 486039475903964569981529 := by
  apply lucas_primality 486039475903964569981529 (3 : ZMod 486039475903964569981529)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (8893, 1), (4391851, 1), (26365356943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (8893, 1), (4391851, 1), (26365356943, 1)] : List FactorBlock).map factorBlockValue).prod) = 486039475903964569981529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_59
      · exact prime_oneHundredFiftyOneES_8893
      · exact prime_oneHundredFiftyOneES_4391851
      · exact prime_oneHundredFiftyOneES_26365356943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 486039475903964569981529) ^ 243019737951982284990764 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 486039475903964569981529) ^ 8237957218711263897992 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 486039475903964569981529) ^ 54654163488582544696 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 486039475903964569981529) ^ 110668480306814728 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 486039475903964569981529) ^ 18434777005096 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_613529292792279042100433 : Nat.Prime 613529292792279042100433 := by
  apply lucas_primality 613529292792279042100433 (3 : ZMod 613529292792279042100433)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (53, 1), (1277, 1), (6857, 1), (15401, 1), (766421083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (53, 1), (1277, 1), (6857, 1), (15401, 1), (766421083, 1)] : List FactorBlock).map factorBlockValue).prod) = 613529292792279042100433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_53
      · exact prime_oneHundredFiftyOneES_1277
      · exact prime_oneHundredFiftyOneES_6857
      · exact prime_oneHundredFiftyOneES_15401
      · exact prime_oneHundredFiftyOneES_766421083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 613529292792279042100433) ^ 306764646396139521050216 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 613529292792279042100433) ^ 87647041827468434585776 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 613529292792279042100433) ^ 11576024392307151737744 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 613529292792279042100433) ^ 480445804849083040016 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 613529292792279042100433) ^ 89474885925664144976 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 613529292792279042100433) ^ 39836977650300567632 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 613529292792279042100433) ^ 800512024526704 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_722870630416403212441603 : Nat.Prime 722870630416403212441603 := by
  apply lucas_primality 722870630416403212441603 (2 : ZMod 722870630416403212441603)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (227, 1), (1907, 1), (15727, 1), (570854197619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (227, 1), (1907, 1), (15727, 1), (570854197619, 1)] : List FactorBlock).map factorBlockValue).prod) = 722870630416403212441603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_227
      · exact prime_oneHundredFiftyOneES_1907
      · exact prime_oneHundredFiftyOneES_15727
      · exact prime_oneHundredFiftyOneES_570854197619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 722870630416403212441603) ^ 361435315208201606220801 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 722870630416403212441603) ^ 240956876805467737480534 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 722870630416403212441603) ^ 23318407432787200401342 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 722870630416403212441603) ^ 3184452116371820319126 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 722870630416403212441603) ^ 379061683490510336886 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 722870630416403212441603) ^ 45963669512074980126 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 722870630416403212441603) ^ 1266296426358 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_886468272370106097515297 : Nat.Prime 886468272370106097515297 := by
  apply lucas_primality 886468272370106097515297 (3 : ZMod 886468272370106097515297)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5023, 1), (4161257, 1), (1325334493423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5023, 1), (4161257, 1), (1325334493423, 1)] : List FactorBlock).map factorBlockValue).prod) = 886468272370106097515297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5023
      · exact prime_oneHundredFiftyOneES_4161257
      · exact prime_oneHundredFiftyOneES_1325334493423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 886468272370106097515297) ^ 443234136185053048757648 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 886468272370106097515297) ^ 176481838019133206752 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 886468272370106097515297) ^ 213028965134839328 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 886468272370106097515297) ^ 668863805152 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_947389561970781520273279 : Nat.Prime 947389561970781520273279 := by
  apply lucas_primality 947389561970781520273279 (6 : ZMod 947389561970781520273279)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (653, 1), (241804380288611924521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (653, 1), (241804380288611924521, 1)] : List FactorBlock).map factorBlockValue).prod) = 947389561970781520273279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_653
      · exact prime_oneHundredFiftyOneES_241804380288611924521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 947389561970781520273279) ^ 473694780985390760136639 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 947389561970781520273279) ^ 315796520656927173424426 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 947389561970781520273279) ^ 1450826281731671547126 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (6 : ZMod 947389561970781520273279) ^ 3918 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2508040172794692140407637 : Nat.Prime 2508040172794692140407637 := by
  apply lucas_primality 2508040172794692140407637 (2 : ZMod 2508040172794692140407637)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (503, 1), (1246540841349250566803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (503, 1), (1246540841349250566803, 1)] : List FactorBlock).map factorBlockValue).prod) = 2508040172794692140407637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_503
      · exact prime_oneHundredFiftyOneES_1246540841349250566803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2508040172794692140407637) ^ 1254020086397346070203818 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2508040172794692140407637) ^ 4986163365397002267212 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2508040172794692140407637) ^ 2012 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_3103871957360146508001523 : Nat.Prime 3103871957360146508001523 := by
  apply lucas_primality 3103871957360146508001523 (2 : ZMod 3103871957360146508001523)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (55779827, 1), (1324882439496983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (55779827, 1), (1324882439496983, 1)] : List FactorBlock).map factorBlockValue).prod) = 3103871957360146508001523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_55779827
      · exact prime_oneHundredFiftyOneES_1324882439496983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3103871957360146508001523) ^ 1551935978680073254000761 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 3103871957360146508001523) ^ 1034623985786715502667174 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 3103871957360146508001523) ^ 443410279622878072571646 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 3103871957360146508001523) ^ 55645062458873286 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 3103871957360146508001523) ^ 2342752734 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_3193372558305777521361899 : Nat.Prime 3193372558305777521361899 := by
  apply lucas_primality 3193372558305777521361899 (2 : ZMod 3193372558305777521361899)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (349, 1), (3142041103, 1), (208010024081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (349, 1), (3142041103, 1), (208010024081, 1)] : List FactorBlock).map factorBlockValue).prod) = 3193372558305777521361899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_349
      · exact prime_oneHundredFiftyOneES_3142041103
      · exact prime_oneHundredFiftyOneES_208010024081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3193372558305777521361899) ^ 1596686279152888760680949 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 3193372558305777521361899) ^ 456196079757968217337414 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 3193372558305777521361899) ^ 9150064636979305218802 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 3193372558305777521361899) ^ 1016336977659766 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 3193372558305777521361899) ^ 15352012829258 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_3688324852269042323751407 : Nat.Prime 3688324852269042323751407 := by
  apply lucas_primality 3688324852269042323751407 (5 : ZMod 3688324852269042323751407)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (16566417313, 1), (15902761000433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (16566417313, 1), (15902761000433, 1)] : List FactorBlock).map factorBlockValue).prod) = 3688324852269042323751407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_16566417313
      · exact prime_oneHundredFiftyOneES_15902761000433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3688324852269042323751407) ^ 1844162426134521161875703 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 3688324852269042323751407) ^ 526903550324148903393058 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 3688324852269042323751407) ^ 222638654006062 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 3688324852269042323751407) ^ 231929842382 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_4586903892588031514753741 : Nat.Prime 4586903892588031514753741 := by
  apply lucas_primality 4586903892588031514753741 (2 : ZMod 4586903892588031514753741)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (229345194629401575737687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (229345194629401575737687, 1)] : List FactorBlock).map factorBlockValue).prod) = 4586903892588031514753741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_229345194629401575737687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4586903892588031514753741) ^ 2293451946294015757376870 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 4586903892588031514753741) ^ 917380778517606302950748 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 4586903892588031514753741) ^ 20 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_5156325443346028148408977 : Nat.Prime 5156325443346028148408977 := by
  apply lucas_primality 5156325443346028148408977 (7 : ZMod 5156325443346028148408977)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (1951, 1), (6117856753595055893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (1951, 1), (6117856753595055893, 1)] : List FactorBlock).map factorBlockValue).prod) = 5156325443346028148408977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_1951
      · exact prime_oneHundredFiftyOneES_6117856753595055893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5156325443346028148408977) ^ 2578162721673014074204488 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 5156325443346028148408977) ^ 1718775147782009382802992 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 5156325443346028148408977) ^ 2642914117553064145776 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 5156325443346028148408977) ^ 842832 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_10926146000338220610454471 : Nat.Prime 10926146000338220610454471 := by
  apply lucas_primality 10926146000338220610454471 (15 : ZMod 10926146000338220610454471)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (28015758975226206693473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (28015758975226206693473, 1)] : List FactorBlock).map factorBlockValue).prod) = 10926146000338220610454471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_28015758975226206693473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 10926146000338220610454471) ^ 5463073000169110305227235 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (15 : ZMod 10926146000338220610454471) ^ 3642048666779406870151490 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (15 : ZMod 10926146000338220610454471) ^ 2185229200067644122090894 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (15 : ZMod 10926146000338220610454471) ^ 840472769256786200804190 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (15 : ZMod 10926146000338220610454471) ^ 390 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_12997619184530483185599971 : Nat.Prime 12997619184530483185599971 := by
  apply lucas_primality 12997619184530483185599971 (2 : ZMod 12997619184530483185599971)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (22961446511, 1), (2979277546433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (22961446511, 1), (2979277546433, 1)] : List FactorBlock).map factorBlockValue).prod) = 12997619184530483185599971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_19
      · exact prime_oneHundredFiftyOneES_22961446511
      · exact prime_oneHundredFiftyOneES_2979277546433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12997619184530483185599971) ^ 6498809592265241592799985 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 12997619184530483185599971) ^ 2599523836906096637119994 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 12997619184530483185599971) ^ 684085220238446483452630 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 12997619184530483185599971) ^ 566062733822270 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 12997619184530483185599971) ^ 4362674837090 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_19632937369352929347213857 : Nat.Prime 19632937369352929347213857 := by
  apply lucas_primality 19632937369352929347213857 (3 : ZMod 19632937369352929347213857)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (613529292792279042100433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (613529292792279042100433, 1)] : List FactorBlock).map factorBlockValue).prod) = 19632937369352929347213857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_613529292792279042100433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 19632937369352929347213857) ^ 9816468684676464673606928 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 19632937369352929347213857) ^ 32 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_20555244617101460743145147 : Nat.Prime 20555244617101460743145147 := by
  apply lucas_primality 20555244617101460743145147 (2 : ZMod 20555244617101460743145147)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8316857, 1), (1235757968250593989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8316857, 1), (1235757968250593989, 1)] : List FactorBlock).map factorBlockValue).prod) = 20555244617101460743145147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_8316857
      · exact prime_oneHundredFiftyOneES_1235757968250593989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20555244617101460743145147) ^ 10277622308550730371572573 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 20555244617101460743145147) ^ 2471515936501187978 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 20555244617101460743145147) ^ 16633714 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_37246463488321758096018277 : Nat.Prime 37246463488321758096018277 := by
  apply lucas_primality 37246463488321758096018277 (5 : ZMod 37246463488321758096018277)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3103871957360146508001523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3103871957360146508001523, 1)] : List FactorBlock).map factorBlockValue).prod) = 37246463488321758096018277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_3103871957360146508001523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 37246463488321758096018277) ^ 18623231744160879048009138 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 37246463488321758096018277) ^ 12415487829440586032006092 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 37246463488321758096018277) ^ 12 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_83852653593013709043783749 : Nat.Prime 83852653593013709043783749 := by
  apply lucas_primality 83852653593013709043783749 (2 : ZMod 83852653593013709043783749)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (37, 1), (53, 1), (59, 1), (1489, 1), (4663, 1), (10531, 1), (20479159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (37, 1), (53, 1), (59, 1), (1489, 1), (4663, 1), (10531, 1), (20479159, 1)] : List FactorBlock).map factorBlockValue).prod) = 83852653593013709043783749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_37
      · exact prime_oneHundredFiftyOneES_53
      · exact prime_oneHundredFiftyOneES_59
      · exact prime_oneHundredFiftyOneES_1489
      · exact prime_oneHundredFiftyOneES_4663
      · exact prime_oneHundredFiftyOneES_10531
      · exact prime_oneHundredFiftyOneES_20479159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 83852653593013709043783749) ^ 41926326796506854521891874 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 83852653593013709043783749) ^ 7622968508455791731253068 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 83852653593013709043783749) ^ 2266287934946316460642804 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 83852653593013709043783749) ^ 1582125539490824698939316 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 83852653593013709043783749) ^ 1421231416830740831250572 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 83852653593013709043783749) ^ 56314743850244263964932 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 83852653593013709043783749) ^ 17982554920225972344796 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 83852653593013709043783749) ^ 7962458797171561014508 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 83852653593013709043783749) ^ 4094535991102647772 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_91738077851760630295074821 : Nat.Prime 91738077851760630295074821 := by
  apply lucas_primality 91738077851760630295074821 (2 : ZMod 91738077851760630295074821)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4586903892588031514753741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4586903892588031514753741, 1)] : List FactorBlock).map factorBlockValue).prod) = 91738077851760630295074821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_4586903892588031514753741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 91738077851760630295074821) ^ 45869038925880315147537410 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 91738077851760630295074821) ^ 18347615570352126059014964 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 91738077851760630295074821) ^ 20 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_97393507637493827907373487 : Nat.Prime 97393507637493827907373487 := by
  apply lucas_primality 97393507637493827907373487 (5 : ZMod 97393507637493827907373487)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (281, 1), (691, 1), (19777, 1), (975465420257833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (281, 1), (691, 1), (19777, 1), (975465420257833, 1)] : List FactorBlock).map factorBlockValue).prod) = 97393507637493827907373487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_281
      · exact prime_oneHundredFiftyOneES_691
      · exact prime_oneHundredFiftyOneES_19777
      · exact prime_oneHundredFiftyOneES_975465420257833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97393507637493827907373487) ^ 48696753818746913953686743 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 97393507637493827907373487) ^ 7491808279807217531336422 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 97393507637493827907373487) ^ 346596112588946006787806 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 97393507637493827907373487) ^ 140945741877704526638746 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 97393507637493827907373487) ^ 4924584499038975977518 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 97393507637493827907373487) ^ 99843116542 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_260997513888196179172829827 : Nat.Prime 260997513888196179172829827 := by
  apply lucas_primality 260997513888196179172829827 (5 : ZMod 260997513888196179172829827)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (17, 1), (311, 1), (461, 1), (12347, 1), (5948495845393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (17, 1), (311, 1), (461, 1), (12347, 1), (5948495845393, 1)] : List FactorBlock).map factorBlockValue).prod) = 260997513888196179172829827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_17
      · exact prime_oneHundredFiftyOneES_311
      · exact prime_oneHundredFiftyOneES_461
      · exact prime_oneHundredFiftyOneES_12347
      · exact prime_oneHundredFiftyOneES_5948495845393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 260997513888196179172829827) ^ 130498756944098089586414913 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 260997513888196179172829827) ^ 86999171296065393057609942 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 260997513888196179172829827) ^ 15352794934599775245460578 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 260997513888196179172829827) ^ 839220301891306042356366 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 260997513888196179172829827) ^ 566155127740121863715466 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 260997513888196179172829827) ^ 21138536801506129357158 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 260997513888196179172829827) ^ 43876220253282 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_304126574956603384249089611 : Nat.Prime 304126574956603384249089611 := by
  apply lucas_primality 304126574956603384249089611 (2 : ZMod 304126574956603384249089611)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (7321, 1), (101321149302075680801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (7321, 1), (101321149302075680801, 1)] : List FactorBlock).map factorBlockValue).prod) = 304126574956603384249089611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_41
      · exact prime_oneHundredFiftyOneES_7321
      · exact prime_oneHundredFiftyOneES_101321149302075680801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 304126574956603384249089611) ^ 152063287478301692124544805 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 304126574956603384249089611) ^ 60825314991320676849817922 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 304126574956603384249089611) ^ 7417721340404960591441210 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 304126574956603384249089611) ^ 41541671213851029128410 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 304126574956603384249089611) ^ 3001610 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_842086318393991446010450951 : Nat.Prime 842086318393991446010450951 := by
  apply lucas_primality 842086318393991446010450951 (13 : ZMod 842086318393991446010450951)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (23, 1), (53, 1), (137, 1), (14406692752208753239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (23, 1), (53, 1), (137, 1), (14406692752208753239, 1)] : List FactorBlock).map factorBlockValue).prod) = 842086318393991446010450951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_23
      · exact prime_oneHundredFiftyOneES_53
      · exact prime_oneHundredFiftyOneES_137
      · exact prime_oneHundredFiftyOneES_14406692752208753239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 842086318393991446010450951) ^ 421043159196995723005225475 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 842086318393991446010450951) ^ 168417263678798289202090190 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 842086318393991446010450951) ^ 120298045484855920858635850 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 842086318393991446010450951) ^ 36612448625825715043932650 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 842086318393991446010450951) ^ 15888421101773423509631150 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 842086318393991446010450951) ^ 6146615462729864569419350 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (13 : ZMod 842086318393991446010450951) ^ 58451050 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_954664703206022387990457763 : Nat.Prime 954664703206022387990457763 := by
  apply lucas_primality 954664703206022387990457763 (5 : ZMod 954664703206022387990457763)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (863, 1), (123307, 1), (795127, 1), (1880462109161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (863, 1), (123307, 1), (795127, 1), (1880462109161, 1)] : List FactorBlock).map factorBlockValue).prod) = 954664703206022387990457763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_863
      · exact prime_oneHundredFiftyOneES_123307
      · exact prime_oneHundredFiftyOneES_795127
      · exact prime_oneHundredFiftyOneES_1880462109161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 954664703206022387990457763) ^ 477332351603011193995228881 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 954664703206022387990457763) ^ 318221567735340795996819254 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 954664703206022387990457763) ^ 1106216342069550855145374 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 954664703206022387990457763) ^ 7742177680148105038566 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 954664703206022387990457763) ^ 1200644303621965281006 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (5 : ZMod 954664703206022387990457763) ^ 507675585993042 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1137084710188064882510927399 : Nat.Prime 1137084710188064882510927399 := by
  apply lucas_primality 1137084710188064882510927399 (7 : ZMod 1137084710188064882510927399)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (101, 1), (184351, 1), (984995528105272279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (101, 1), (184351, 1), (984995528105272279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1137084710188064882510927399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_31
      · exact prime_oneHundredFiftyOneES_101
      · exact prime_oneHundredFiftyOneES_184351
      · exact prime_oneHundredFiftyOneES_984995528105272279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1137084710188064882510927399) ^ 568542355094032441255463699 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 1137084710188064882510927399) ^ 36680151941550480080997658 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 1137084710188064882510927399) ^ 11258264457307573094167598 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 1137084710188064882510927399) ^ 6168041996995215011098 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 1137084710188064882510927399) ^ 1154405962 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1322387403700193974475671123 : Nat.Prime 1322387403700193974475671123 := by
  apply lucas_primality 1322387403700193974475671123 (3 : ZMod 1322387403700193974475671123)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (821, 1), (1367, 1), (1140925213, 1), (8196327617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (821, 1), (1367, 1), (1140925213, 1), (8196327617, 1)] : List FactorBlock).map factorBlockValue).prod) = 1322387403700193974475671123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_821
      · exact prime_oneHundredFiftyOneES_1367
      · exact prime_oneHundredFiftyOneES_1140925213
      · exact prime_oneHundredFiftyOneES_8196327617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1322387403700193974475671123) ^ 661193701850096987237835561 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1322387403700193974475671123) ^ 440795801233397991491890374 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1322387403700193974475671123) ^ 188912486242884853496524446 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1322387403700193974475671123) ^ 1610703293179286205207882 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1322387403700193974475671123) ^ 967364596708261868672766 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1322387403700193974475671123) ^ 1159048278215404794 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 1322387403700193974475671123) ^ 161339012481325266 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_1940459777168762897328430453 : Nat.Prime 1940459777168762897328430453 := by
  apply lucas_primality 1940459777168762897328430453 (2 : ZMod 1940459777168762897328430453)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (81153949, 1), (1992570705717971179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (81153949, 1), (1992570705717971179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1940459777168762897328430453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_81153949
      · exact prime_oneHundredFiftyOneES_1992570705717971179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1940459777168762897328430453) ^ 970229888584381448664215226 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1940459777168762897328430453) ^ 646819925722920965776143484 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1940459777168762897328430453) ^ 23910848468615654148 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 1940459777168762897328430453) ^ 973847388 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_2975371658325436442570260027 : Nat.Prime 2975371658325436442570260027 := by
  apply lucas_primality 2975371658325436442570260027 (2 : ZMod 2975371658325436442570260027)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (73, 1), (38717179, 1), (15950368458385583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (73, 1), (38717179, 1), (15950368458385583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2975371658325436442570260027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_11
      · exact prime_oneHundredFiftyOneES_73
      · exact prime_oneHundredFiftyOneES_38717179
      · exact prime_oneHundredFiftyOneES_15950368458385583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2975371658325436442570260027) ^ 1487685829162718221285130013 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2975371658325436442570260027) ^ 991790552775145480856753342 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2975371658325436442570260027) ^ 270488332575039676597296366 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2975371658325436442570260027) ^ 40758515867471732090003562 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2975371658325436442570260027) ^ 76848875232501738894 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 2975371658325436442570260027) ^ 186539368422 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_3245859990900476119167556393 : Nat.Prime 3245859990900476119167556393 := by
  apply lucas_primality 3245859990900476119167556393 (10 : ZMod 3245859990900476119167556393)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (73, 1), (38717179, 1), (15950368458385583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (73, 1), (38717179, 1), (15950368458385583, 1)] : List FactorBlock).map factorBlockValue).prod) = 3245859990900476119167556393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_73
      · exact prime_oneHundredFiftyOneES_38717179
      · exact prime_oneHundredFiftyOneES_15950368458385583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3245859990900476119167556393) ^ 1622929995450238059583778196 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 3245859990900476119167556393) ^ 1081953330300158706389185464 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 3245859990900476119167556393) ^ 44463835491787344098185704 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 3245859990900476119167556393) ^ 83835136617274624248 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (10 : ZMod 3245859990900476119167556393) ^ 203497492824 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_4463057487488154663855390041 : Nat.Prime 4463057487488154663855390041 := by
  apply lucas_primality 4463057487488154663855390041 (3 : ZMod 4463057487488154663855390041)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (151, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (151, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 4463057487488154663855390041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_151
      · exact prime_oneHundredFiftyOneES_171401
      · exact prime_oneHundredFiftyOneES_714027719
      · exact prime_oneHundredFiftyOneES_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4463057487488154663855390041) ^ 2231528743744077331927695020 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 4463057487488154663855390041) ^ 892611497497630932771078008 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 4463057487488154663855390041) ^ 29556672102570560687784040 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 4463057487488154663855390041) ^ 26038689899639760934040 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 4463057487488154663855390041) ^ 6250538135604445160 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 4463057487488154663855390041) ^ 739205792988486760 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_7438429145813591106425650069 : Nat.Prime 7438429145813591106425650069 := by
  apply lucas_primality 7438429145813591106425650069 (2 : ZMod 7438429145813591106425650069)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (349, 1), (43891, 1), (395047, 1), (875516735179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (349, 1), (43891, 1), (395047, 1), (875516735179, 1)] : List FactorBlock).map factorBlockValue).prod) = 7438429145813591106425650069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_13
      · exact prime_oneHundredFiftyOneES_349
      · exact prime_oneHundredFiftyOneES_43891
      · exact prime_oneHundredFiftyOneES_395047
      · exact prime_oneHundredFiftyOneES_875516735179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7438429145813591106425650069) ^ 3719214572906795553212825034 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438429145813591106425650069) ^ 2479476381937863702141883356 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438429145813591106425650069) ^ 572186857370276238955819236 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438429145813591106425650069) ^ 21313550561070461622996132 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438429145813591106425650069) ^ 169475043763267893336348 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438429145813591106425650069) ^ 18829225752413234644044 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 7438429145813591106425650069) ^ 8496044503698492 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_10501311735266246267895035389 : Nat.Prime 10501311735266246267895035389 := by
  apply lucas_primality 10501311735266246267895035389 (2 : ZMod 10501311735266246267895035389)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (6027387371, 1), (6913753737787139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (6027387371, 1), (6913753737787139, 1)] : List FactorBlock).map factorBlockValue).prod) = 10501311735266246267895035389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_6027387371
      · exact prime_oneHundredFiftyOneES_6913753737787139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10501311735266246267895035389) ^ 5250655867633123133947517694 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 10501311735266246267895035389) ^ 3500437245088748755965011796 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 10501311735266246267895035389) ^ 1500187390752320895413576484 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 10501311735266246267895035389) ^ 1742265941922359028 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 10501311735266246267895035389) ^ 1518901617492 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_59507433166508728851405200561 : Nat.Prime 59507433166508728851405200561 := by
  apply lucas_primality 59507433166508728851405200561 (3 : ZMod 59507433166508728851405200561)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (99937039, 1), (1063302200814882359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (99937039, 1), (1063302200814882359, 1)] : List FactorBlock).map factorBlockValue).prod) = 59507433166508728851405200561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_5
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_99937039
      · exact prime_oneHundredFiftyOneES_1063302200814882359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 59507433166508728851405200561) ^ 29753716583254364425702600280 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 59507433166508728851405200561) ^ 11901486633301745770281040112 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 59507433166508728851405200561) ^ 8501061880929818407343600080 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 59507433166508728851405200561) ^ 595449232456334121040 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 59507433166508728851405200561) ^ 55964741840 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_89261149749763093277107800823 : Nat.Prime 89261149749763093277107800823 := by
  apply lucas_primality 89261149749763093277107800823 (3 : ZMod 89261149749763093277107800823)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (383, 1), (947389561970781520273279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (383, 1), (947389561970781520273279, 1)] : List FactorBlock).map factorBlockValue).prod) = 89261149749763093277107800823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_41
      · exact prime_oneHundredFiftyOneES_383
      · exact prime_oneHundredFiftyOneES_947389561970781520273279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 89261149749763093277107800823) ^ 44630574874881546638553900411 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 89261149749763093277107800823) ^ 29753716583254364425702600274 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 89261149749763093277107800823) ^ 2177101213408855933587995142 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 89261149749763093277107800823) ^ 233057832244812253987226634 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (3 : ZMod 89261149749763093277107800823) ^ 94218 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_89261149749763093277107800827 : Nat.Prime 89261149749763093277107800827 := by
  apply lucas_primality 89261149749763093277107800827 (2 : ZMod 89261149749763093277107800827)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (93505567, 1), (68186276125114174277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (93505567, 1), (68186276125114174277, 1)] : List FactorBlock).map factorBlockValue).prod) = 89261149749763093277107800827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_93505567
      · exact prime_oneHundredFiftyOneES_68186276125114174277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 89261149749763093277107800827) ^ 44630574874881546638553900413 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 89261149749763093277107800827) ^ 12751592821394727611015400118 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 89261149749763093277107800827) ^ 954607865751598439878 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (2 : ZMod 89261149749763093277107800827) ^ 1309077938 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyOneES_178522299499526186554215601639 : Nat.Prime 178522299499526186554215601639 := by
  apply lucas_primality 178522299499526186554215601639 (7 : ZMod 178522299499526186554215601639)
  · rw [← oneHundredFiftyOneESFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (2604191, 1), (44113206215350451717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (2604191, 1), (44113206215350451717, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyOneES_2
      · exact prime_oneHundredFiftyOneES_3
      · exact prime_oneHundredFiftyOneES_7
      · exact prime_oneHundredFiftyOneES_37
      · exact prime_oneHundredFiftyOneES_2604191
      · exact prime_oneHundredFiftyOneES_44113206215350451717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 178522299499526186554215601639) ^ 89261149749763093277107800819 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 178522299499526186554215601639) ^ 59507433166508728851405200546 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 178522299499526186554215601639) ^ 25503185642789455222030800234 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 178522299499526186554215601639) ^ 4824927013500707744708529774 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 178522299499526186554215601639) ^ 68551922458654601968218 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide
    · change (7 : ZMod 178522299499526186554215601639) ^ 4046912814 ≠ 1
      rw [← oneHundredFiftyOneESFastPow_eq_pow]
      decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601600 : Nat.totient 178522299499526186554215601600 = 70935599075102811283737600000 := by
  rw [← show ((([(2, 6), (5, 2), (151, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_151, prime_oneHundredFiftyOneES_171401, prime_oneHundredFiftyOneES_714027719, prime_oneHundredFiftyOneES_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601601 : Nat.totient 178522299499526186554215601601 = 173697372476841916927245406320 := by
  rw [← show ((([(37, 1), (18913945111, 1), (255098922259990043, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_37, prime_oneHundredFiftyOneES_18913945111, prime_oneHundredFiftyOneES_255098922259990043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601602 : Nat.totient 178522299499526186554215601602 = 59497999732056837118441495040 := by
  rw [← show ((([(2, 1), (3, 1), (8831, 1), (30497, 1), (79979, 1), (1381332555959039, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_8831, prime_oneHundredFiftyOneES_30497, prime_oneHundredFiftyOneES_79979, prime_oneHundredFiftyOneES_1381332555959039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601603 : Nat.totient 178522299499526186554215601603 = 149232749772916326471764832000 := by
  rw [← show ((([(7, 1), (41, 1), (3191, 1), (20149, 1), (9674538883326363391, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_41, prime_oneHundredFiftyOneES_3191, prime_oneHundredFiftyOneES_20149, prime_oneHundredFiftyOneES_9674538883326363391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601604 : Nat.totient 178522299499526186554215601604 = 78338032251737543721390044160 := by
  rw [← show ((([(2, 2), (11, 1), (29, 1), (7603, 1), (10541737, 1), (1745599586337389, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_11, prime_oneHundredFiftyOneES_29, prime_oneHundredFiftyOneES_7603, prime_oneHundredFiftyOneES_10541737, prime_oneHundredFiftyOneES_1745599586337389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601605 : Nat.totient 178522299499526186554215601605 = 95211893066413966162248320784 := by
  rw [← show ((([(3, 3), (5, 1), (1322387403700193974475671123, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_1322387403700193974475671123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601606 : Nat.totient 178522299499526186554215601606 = 81802761022516854916265760000 := by
  rw [← show ((([(2, 1), (13, 1), (251, 1), (311, 1), (95825264243, 1), (917920329097, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_13, prime_oneHundredFiftyOneES_251, prime_oneHundredFiftyOneES_311, prime_oneHundredFiftyOneES_95825264243, prime_oneHundredFiftyOneES_917920329097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601607 : Nat.totient 178522299499526186554215601607 = 170760460380550114968281863552 := by
  rw [← show ((([(23, 1), (16577044457, 1), (468228165087501737, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_23, prime_oneHundredFiftyOneES_16577044457, prime_oneHundredFiftyOneES_468228165087501737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601608 : Nat.totient 178522299499526186554215601608 = 59507228110588292640883785600 := by
  rw [← show ((([(2, 3), (3, 1), (290201, 1), (25631990054526314886667, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_290201, prime_oneHundredFiftyOneES_25631990054526314886667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601609 : Nat.totient 178522299499526186554215601609 = 178522299499490180997046293520 := by
  rw [← show ((([(4958870350349, 1), (36000598298957741, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_4958870350349, prime_oneHundredFiftyOneES_36000598298957741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601610 : Nat.totient 178522299499526186554215601610 = 59230966684984906959248834880 := by
  rw [← show ((([(2, 1), (5, 1), (7, 3), (31, 1), (26459, 1), (63454617720594891163, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_31, prime_oneHundredFiftyOneES_26459, prime_oneHundredFiftyOneES_63454617720594891163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601611 : Nat.totient 178522299499526186554215601611 = 112127988686791256129753130240 := by
  rw [← show ((([(3, 1), (19, 1), (181, 1), (27891887, 1), (620384794267342009, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_19, prime_oneHundredFiftyOneES_181, prime_oneHundredFiftyOneES_27891887, prime_oneHundredFiftyOneES_620384794267342009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601612 : Nat.totient 178522299499526186554215601612 = 87576977112975110385086898800 := by
  rw [← show ((([(2, 2), (53, 1), (842086318393991446010450951, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_53, prime_oneHundredFiftyOneES_842086318393991446010450951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601613 : Nat.totient 178522299499526186554215601613 = 168020987764259940286320566208 := by
  rw [← show ((([(17, 1), (10501311735266246267895035389, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_17, prime_oneHundredFiftyOneES_10501311735266246267895035389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601614 : Nat.totient 178522299499526186554215601614 = 59485303217395114597462675968 := by
  rw [← show ((([(2, 1), (3, 2), (2689, 1), (3688324852269042323751407, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_2689, prime_oneHundredFiftyOneES_3688324852269042323751407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601615 : Nat.totient 178522299499526186554215601615 = 129834399636019044766702255680 := by
  rw [← show ((([(5, 1), (11, 1), (3245859990900476119167556393, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_11, prime_oneHundredFiftyOneES_3245859990900476119167556393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601616 : Nat.totient 178522299499526186554215601616 = 86376444358606003257017112576 := by
  rw [← show ((([(2, 4), (59, 1), (107, 1), (269, 1), (379, 1), (1326503, 1), (13068837977309, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_59, prime_oneHundredFiftyOneES_107, prime_oneHundredFiftyOneES_269, prime_oneHundredFiftyOneES_379, prime_oneHundredFiftyOneES_1326503, prime_oneHundredFiftyOneES_13068837977309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601617 : Nat.totient 178522299499526186554215601617 = 102001042496472765287321024640 := by
  rw [← show ((([(3, 1), (7, 1), (8719, 1), (4263328073, 1), (228695566762571, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_8719, prime_oneHundredFiftyOneES_4263328073, prime_oneHundredFiftyOneES_228695566762571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601618 : Nat.totient 178522299499526186554215601618 = 87928893778581460513548097920 := by
  rw [← show ((([(2, 1), (67, 1), (18444336737, 1), (72231166965295171, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_67, prime_oneHundredFiftyOneES_18444336737, prime_oneHundredFiftyOneES_72231166965295171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601619 : Nat.totient 178522299499526186554215601619 = 164580967608793001055198247680 := by
  rw [← show ((([(13, 1), (1049, 1), (3181, 1), (4115380189299199259827, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_13, prime_oneHundredFiftyOneES_1049, prime_oneHundredFiftyOneES_3181, prime_oneHundredFiftyOneES_4115380189299199259827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601620 : Nat.totient 178522299499526186554215601620 = 47605946533206983081124160416 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (2975371658325436442570260027, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_2975371658325436442570260027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601621 : Nat.totient 178522299499526186554215601621 = 178438446845933172845171815744 := by
  rw [← show ((([(2129, 1), (83852653593013709043783749, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2129, prime_oneHundredFiftyOneES_83852653593013709043783749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601622 : Nat.totient 178522299499526186554215601622 = 89261135083095262773504964272 := by
  rw [← show ((([(2, 1), (6085987, 1), (14666667830503596750553, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_6085987, prime_oneHundredFiftyOneES_14666667830503596750553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601623 : Nat.totient 178522299499526186554215601623 = 119014860059093991324988427040 := by
  rw [← show ((([(3, 2), (18969767, 1), (1045653911062951359241, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_18969767, prime_oneHundredFiftyOneES_1045653911062951359241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601624 : Nat.totient 178522299499526186554215601624 = 74448843704221041482810572800 := by
  rw [← show ((([(2, 3), (7, 1), (47, 1), (173, 1), (10799177, 1), (66567367, 1), (545391601, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_47, prime_oneHundredFiftyOneES_173, prime_oneHundredFiftyOneES_10799177, prime_oneHundredFiftyOneES_66567367, prime_oneHundredFiftyOneES_545391601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601625 : Nat.totient 178522299499526186554215601625 = 142419674966434793816638464000 := by
  rw [← show ((([(5, 3), (359, 1), (415189, 1), (442516031, 1), (21652755073, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_359, prime_oneHundredFiftyOneES_415189, prime_oneHundredFiftyOneES_442516031, prime_oneHundredFiftyOneES_21652755073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601626 : Nat.totient 178522299499526186554215601626 = 53421577070839208019915436800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (83, 1), (2213, 1), (335029, 1), (43954832492729671, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_11, prime_oneHundredFiftyOneES_83, prime_oneHundredFiftyOneES_2213, prime_oneHundredFiftyOneES_335029, prime_oneHundredFiftyOneES_43954832492729671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601627 : Nat.totient 178522299499526186554215601627 = 178508176994461128157056268800 := by
  rw [← show ((([(12641, 1), (7861716307, 1), (1796361227939321, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_12641, prime_oneHundredFiftyOneES_7861716307, prime_oneHundredFiftyOneES_1796361227939321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601628 : Nat.totient 178522299499526186554215601628 = 89122329902118207654767959920 := by
  rw [← show ((([(2, 2), (643, 1), (4664345611, 1), (14880954384078359, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_643, prime_oneHundredFiftyOneES_4664345611, prime_oneHundredFiftyOneES_14880954384078359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601629 : Nat.totient 178522299499526186554215601629 = 119014865240469220328552704080 := by
  rw [← show ((([(3, 1), (108933283, 1), (546274118687019915221, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_108933283, prime_oneHundredFiftyOneES_546274118687019915221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601630 : Nat.totient 178522299499526186554215601630 = 60218500328144580659458129920 := by
  rw [← show ((([(2, 1), (5, 1), (17, 2), (19, 1), (23, 1), (89, 1), (120844861, 1), (13143014873179, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_17, prime_oneHundredFiftyOneES_19, prime_oneHundredFiftyOneES_23, prime_oneHundredFiftyOneES_89, prime_oneHundredFiftyOneES_120844861, prime_oneHundredFiftyOneES_13143014873179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601631 : Nat.totient 178522299499526186554215601631 = 147005246363522122323288576000 := by
  rw [← show ((([(7, 1), (43, 1), (61, 1), (31741, 1), (322079, 1), (6743381, 1), (141037769, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_43, prime_oneHundredFiftyOneES_61, prime_oneHundredFiftyOneES_31741, prime_oneHundredFiftyOneES_322079, prime_oneHundredFiftyOneES_6743381, prime_oneHundredFiftyOneES_141037769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601632 : Nat.totient 178522299499526186554215601632 = 54771159367060318504597524480 := by
  rw [← show ((([(2, 5), (3, 4), (13, 1), (349, 1), (43891, 1), (395047, 1), (875516735179, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_13, prime_oneHundredFiftyOneES_349, prime_oneHundredFiftyOneES_43891, prime_oneHundredFiftyOneES_395047, prime_oneHundredFiftyOneES_875516735179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601633 : Nat.totient 178522299499526186554215601633 = 169984981463963909514804288000 := by
  rw [← show ((([(29, 1), (73, 1), (9059, 1), (119101, 1), (78158451537654811, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_29, prime_oneHundredFiftyOneES_73, prime_oneHundredFiftyOneES_9059, prime_oneHundredFiftyOneES_119101, prime_oneHundredFiftyOneES_78158451537654811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601634 : Nat.totient 178522299499526186554215601634 = 89261104753163378011733003380 := by
  rw [← show ((([(2, 1), (1983731, 1), (44996599715265372813707, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_1983731, prime_oneHundredFiftyOneES_44996599715265372813707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601635 : Nat.totient 178522299499526186554215601635 = 95160174096217701175412797440 := by
  rw [← show ((([(3, 1), (5, 1), (2309, 1), (9187, 1), (837721, 1), (9946247, 1), (67335629, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_2309, prime_oneHundredFiftyOneES_9187, prime_oneHundredFiftyOneES_837721, prime_oneHundredFiftyOneES_9946247, prime_oneHundredFiftyOneES_67335629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601636 : Nat.totient 178522299499526186554215601636 = 88115659160130176248093916160 := by
  rw [← show ((([(2, 2), (103, 1), (317, 1), (2901739, 1), (471061539634278881, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_103, prime_oneHundredFiftyOneES_317, prime_oneHundredFiftyOneES_2901739, prime_oneHundredFiftyOneES_471061539634278881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601637 : Nat.totient 178522299499526186554215601637 = 162160275972906907692937374720 := by
  rw [← show ((([(11, 1), (1223, 1), (7100897, 1), (1868788344955895257, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_11, prime_oneHundredFiftyOneES_1223, prime_oneHundredFiftyOneES_7100897, prime_oneHundredFiftyOneES_1868788344955895257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601638 : Nat.totient 178522299499526186554215601638 = 49627801653387908913053297280 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (37, 1), (2604191, 1), (44113206215350451717, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_37, prime_oneHundredFiftyOneES_2604191, prime_oneHundredFiftyOneES_44113206215350451717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601639 : Nat.totient 178522299499526186554215601639 = 178522299499526186554215601638 := by
  rw [← show ((([(178522299499526186554215601639, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_178522299499526186554215601639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601640 : Nat.totient 178522299499526186554215601640 = 71408919799810474621686240640 := by
  rw [← show ((([(2, 3), (5, 1), (4463057487488154663855390041, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_4463057487488154663855390041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601641 : Nat.totient 178522299499526186554215601641 = 115136674158068077888651677120 := by
  rw [← show ((([(3, 2), (31, 1), (2953, 1), (216682991113497587113543, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_31, prime_oneHundredFiftyOneES_2953, prime_oneHundredFiftyOneES_216682991113497587113543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601642 : Nat.totient 178522299499526186554215601642 = 89260263281490723171010184832 := by
  rw [← show ((([(2, 1), (100693, 1), (886468272370106097515297, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_100693, prime_oneHundredFiftyOneES_886468272370106097515297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601643 : Nat.totient 178522299499526186554215601643 = 177385214789338121671704674088 := by
  rw [← show ((([(157, 1), (1137084710188064882510927399, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_157, prime_oneHundredFiftyOneES_1137084710188064882510927399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601644 : Nat.totient 178522299499526186554215601644 = 57904450027654166519102751360 := by
  rw [← show ((([(2, 2), (3, 1), (41, 1), (383, 1), (947389561970781520273279, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_41, prime_oneHundredFiftyOneES_383, prime_oneHundredFiftyOneES_947389561970781520273279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601645 : Nat.totient 178522299499526186554215601645 = 111353864116225806826173480960 := by
  rw [← show ((([(5, 1), (7, 1), (13, 1), (71, 1), (2089, 1), (25848413, 1), (102341175912377, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_13, prime_oneHundredFiftyOneES_71, prime_oneHundredFiftyOneES_2089, prime_oneHundredFiftyOneES_25848413, prime_oneHundredFiftyOneES_102341175912377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601646 : Nat.totient 178522299499526186554215601646 = 89261149749763093277107800822 := by
  rw [← show ((([(2, 1), (89261149749763093277107800823, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_89261149749763093277107800823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601647 : Nat.totient 178522299499526186554215601647 = 109741007486726463691210752000 := by
  rw [← show ((([(3, 1), (17, 1), (97, 1), (127, 1), (479, 1), (7001, 1), (84732739892975197, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_17, prime_oneHundredFiftyOneES_97, prime_oneHundredFiftyOneES_127, prime_oneHundredFiftyOneES_479, prime_oneHundredFiftyOneES_7001, prime_oneHundredFiftyOneES_84732739892975197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601648 : Nat.totient 178522299499526186554215601648 = 81102896062761765147210374400 := by
  rw [← show ((([(2, 4), (11, 1), (1861, 1), (37155304699, 1), (14669408552507, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_11, prime_oneHundredFiftyOneES_1861, prime_oneHundredFiftyOneES_37155304699, prime_oneHundredFiftyOneES_14669408552507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601649 : Nat.totient 178522299499526186554215601649 = 167829238843502251419547416000 := by
  rw [← show ((([(19, 1), (131, 1), (27701, 1), (3343243, 1), (774469259700287, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_19, prime_oneHundredFiftyOneES_131, prime_oneHundredFiftyOneES_27701, prime_oneHundredFiftyOneES_3343243, prime_oneHundredFiftyOneES_774469259700287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601650 : Nat.totient 178522299499526186554215601650 = 47587945925148753868756992000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 2), (2753, 1), (83833, 1), (338563, 1), (5077141237451, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_2753, prime_oneHundredFiftyOneES_83833, prime_oneHundredFiftyOneES_338563, prime_oneHundredFiftyOneES_5077141237451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601651 : Nat.totient 178522299499526186554215601651 = 177756100985444200969006338432 := by
  rw [← show ((([(233, 1), (21193043, 1), (36152907659716847929, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_233, prime_oneHundredFiftyOneES_21193043, prime_oneHundredFiftyOneES_36152907659716847929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601652 : Nat.totient 178522299499526186554215601652 = 76509556110133052163600242592 := by
  rw [← show ((([(2, 2), (7, 1), (93505567, 1), (68186276125114174277, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_93505567, prime_oneHundredFiftyOneES_68186276125114174277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601653 : Nat.totient 178522299499526186554215601653 = 112399143079845729111378454080 := by
  rw [← show ((([(3, 1), (23, 1), (79, 1), (763043, 1), (42920747567267744821, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_23, prime_oneHundredFiftyOneES_79, prime_oneHundredFiftyOneES_763043, prime_oneHundredFiftyOneES_42920747567267744821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601654 : Nat.totient 178522299499526186554215601654 = 89261149749763093277107800826 := by
  rw [← show ((([(2, 1), (89261149749763093277107800827, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_89261149749763093277107800827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601655 : Nat.totient 178522299499526186554215601655 = 142569712089494262173264714400 := by
  rw [← show ((([(5, 1), (743, 1), (2551, 1), (18837496972873297153067, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_743, prime_oneHundredFiftyOneES_2551, prime_oneHundredFiftyOneES_18837496972873297153067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601656 : Nat.totient 178522299499526186554215601656 = 59507433166508728851405200544 := by
  rw [← show ((([(2, 3), (3, 1), (7438429145813591106425650069, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_7438429145813591106425650069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601657 : Nat.totient 178522299499526186554215601657 = 178218172924569583169966511460 := by
  rw [← show ((([(587, 1), (304126574956603384249089611, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_587, prime_oneHundredFiftyOneES_304126574956603384249089611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601658 : Nat.totient 178522299499526186554215601658 = 82394627753999829060078796800 := by
  rw [← show ((([(2, 1), (13, 1), (295073, 1), (174695441, 1), (133201182612481, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_13, prime_oneHundredFiftyOneES_295073, prime_oneHundredFiftyOneES_174695441, prime_oneHundredFiftyOneES_133201182612481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601659 : Nat.totient 178522299499526186554215601659 = 92738856878439573109703472000 := by
  rw [← show ((([(3, 3), (7, 2), (11, 1), (20929484203, 1), (586113085360601, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_11, prime_oneHundredFiftyOneES_20929484203, prime_oneHundredFiftyOneES_586113085360601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601660 : Nat.totient 178522299499526186554215601660 = 71388855478428117084562951104 := by
  rw [← show ((([(2, 2), (5, 1), (3559, 1), (2508040172794692140407637, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_3559, prime_oneHundredFiftyOneES_2508040172794692140407637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601661 : Nat.totient 178522299499526186554215601661 = 178485053036037864796119578592 := by
  rw [← show ((([(4793, 1), (37246463488321758096018277, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_4793, prime_oneHundredFiftyOneES_37246463488321758096018277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601662 : Nat.totient 178522299499526186554215601662 = 57069844817742738364220909568 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (149, 1), (68794993, 1), (100092174581997509, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_29, prime_oneHundredFiftyOneES_149, prime_oneHundredFiftyOneES_68794993, prime_oneHundredFiftyOneES_100092174581997509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601663 : Nat.totient 178522299499526186554215601663 = 176941687931871665067016012800 := by
  rw [← show ((([(113, 1), (438601, 1), (485059, 1), (7425912782854589, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_113, prime_oneHundredFiftyOneES_438601, prime_oneHundredFiftyOneES_485059, prime_oneHundredFiftyOneES_7425912782854589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601664 : Nat.totient 178522299499526186554215601664 = 84002482225175259615164366848 := by
  rw [← show ((([(2, 9), (17, 1), (10487, 1), (113631509, 1), (17211691285577, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_17, prime_oneHundredFiftyOneES_10487, prime_oneHundredFiftyOneES_113631509, prime_oneHundredFiftyOneES_17211691285577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601665 : Nat.totient 178522299499526186554215601665 = 93223624097261390602934188800 := by
  rw [← show ((([(3, 1), (5, 1), (53, 1), (487, 1), (461101337929632550861301, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_53, prime_oneHundredFiftyOneES_487, prime_oneHundredFiftyOneES_461101337929632550861301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601666 : Nat.totient 178522299499526186554215601666 = 75959128461257801884321950960 := by
  rw [← show ((([(2, 1), (7, 1), (139, 1), (91738077851760630295074821, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_139, prime_oneHundredFiftyOneES_91738077851760630295074821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601667 : Nat.totient 178522299499526186554215601667 = 178522299499519214864550698496 := by
  rw [← show ((([(25701497786113, 1), (6945988167117059, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_25701497786113, prime_oneHundredFiftyOneES_6945988167117059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601668 : Nat.totient 178522299499526186554215601668 = 56375462999850374701331242416 := by
  rw [← show ((([(2, 2), (3, 2), (19, 1), (260997513888196179172829827, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_19, prime_oneHundredFiftyOneES_260997513888196179172829827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601669 : Nat.totient 178522299499526186554215601669 = 178511373353525848333605130860 := by
  rw [← show ((([(16339, 1), (10926146000338220610454471, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_16339, prime_oneHundredFiftyOneES_10926146000338220610454471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601670 : Nat.totient 178522299499526186554215601670 = 64645579661744147733670203200 := by
  rw [← show ((([(2, 1), (5, 1), (11, 2), (239, 1), (881393531, 1), (700389041400803, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_11, prime_oneHundredFiftyOneES_239, prime_oneHundredFiftyOneES_881393531, prime_oneHundredFiftyOneES_700389041400803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601671 : Nat.totient 178522299499526186554215601671 = 107522432431793186009740328544 := by
  rw [← show ((([(3, 1), (13, 1), (47, 1), (97393507637493827907373487, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_13, prime_oneHundredFiftyOneES_47, prime_oneHundredFiftyOneES_97393507637493827907373487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601672 : Nat.totient 178522299499526186554215601672 = 86006691568260585917486208000 := by
  rw [← show ((([(2, 3), (31, 1), (241, 1), (5171, 1), (577629295402566797749, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_31, prime_oneHundredFiftyOneES_241, prime_oneHundredFiftyOneES_5171, prime_oneHundredFiftyOneES_577629295402566797749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601673 : Nat.totient 178522299499526186554215601673 = 151442242127217498302592799680 := by
  rw [← show ((([(7, 1), (167, 1), (283, 1), (1231, 1), (438362578281810567829, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_167, prime_oneHundredFiftyOneES_283, prime_oneHundredFiftyOneES_1231, prime_oneHundredFiftyOneES_438362578281810567829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601674 : Nat.totient 178522299499526186554215601674 = 57659718754787517489170649600 := by
  rw [← show ((([(2, 1), (3, 1), (43, 1), (137, 1), (1459, 1), (4099861, 1), (844360239481331, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_43, prime_oneHundredFiftyOneES_137, prime_oneHundredFiftyOneES_1459, prime_oneHundredFiftyOneES_4099861, prime_oneHundredFiftyOneES_844360239481331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601675 : Nat.totient 178522299499526186554215601675 = 136071123038185906703544975360 := by
  rw [← show ((([(5, 2), (37, 1), (59, 1), (257, 1), (4790339, 1), (2657047731035063, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_37, prime_oneHundredFiftyOneES_59, prime_oneHundredFiftyOneES_257, prime_oneHundredFiftyOneES_4790339, prime_oneHundredFiftyOneES_2657047731035063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601676 : Nat.totient 178522299499526186554215601676 = 85380230195425567482450939888 := by
  rw [← show ((([(2, 2), (23, 1), (1940459777168762897328430453, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_23, prime_oneHundredFiftyOneES_1940459777168762897328430453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601677 : Nat.totient 178522299499526186554215601677 = 119010607274383181597783577600 := by
  rw [← show ((([(3, 2), (71353, 1), (83701, 1), (101789, 1), (32629185343309, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_71353, prime_oneHundredFiftyOneES_83701, prime_oneHundredFiftyOneES_101789, prime_oneHundredFiftyOneES_32629185343309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601678 : Nat.totient 178522299499526186554215601678 = 89261148924535618938766813920 := by
  rw [← show ((([(2, 1), (120699013, 1), (1043178431, 1), (708924783013, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_120699013, prime_oneHundredFiftyOneES_1043178431, prime_oneHundredFiftyOneES_708924783013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601679 : Nat.totient 178522299499526186554215601679 = 178477746890779280734268695776 := by
  rw [← show ((([(4007, 1), (190899756349, 1), (233382214117453, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_4007, prime_oneHundredFiftyOneES_190899756349, prime_oneHundredFiftyOneES_233382214117453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601680 : Nat.totient 178522299499526186554215601680 = 40805096620155083203958631936 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (7, 1), (99937039, 1), (1063302200814882359, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_99937039, prime_oneHundredFiftyOneES_1063302200814882359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601681 : Nat.totient 178522299499526186554215601681 = 152746352512963582078473241920 := by
  rw [← show ((([(11, 1), (17, 1), (954664703206022387990457763, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_11, prime_oneHundredFiftyOneES_17, prime_oneHundredFiftyOneES_954664703206022387990457763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601682 : Nat.totient 178522299499526186554215601682 = 89196145789283697456054021888 := by
  rw [← show ((([(2, 1), (1867, 1), (5189, 1), (71698769, 1), (128505817458703, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_1867, prime_oneHundredFiftyOneES_5189, prime_oneHundredFiftyOneES_71698769, prime_oneHundredFiftyOneES_128505817458703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601683 : Nat.totient 178522299499526186554215601683 = 119014866333017457702810401120 := by
  rw [← show ((([(3, 1), (59507433166508728851405200561, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_59507433166508728851405200561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601684 : Nat.totient 178522299499526186554215601684 = 82394082926825674398003216384 := by
  rw [← show ((([(2, 2), (13, 1), (99929, 1), (34355603921000484681473, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_13, prime_oneHundredFiftyOneES_99929, prime_oneHundredFiftyOneES_34355603921000484681473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601685 : Nat.totient 178522299499526186554215601685 = 137254858588641902439935683200 := by
  rw [← show ((([(5, 1), (41, 1), (67, 1), (12997619184530483185599971, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_41, prime_oneHundredFiftyOneES_67, prime_oneHundredFiftyOneES_12997619184530483185599971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601686 : Nat.totient 178522299499526186554215601686 = 59331240757159327987061391360 := by
  rw [← show ((([(2, 1), (3, 3), (673, 1), (677, 1), (18845921, 1), (385014967634749, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_673, prime_oneHundredFiftyOneES_677, prime_oneHundredFiftyOneES_18845921, prime_oneHundredFiftyOneES_385014967634749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601687 : Nat.totient 178522299499526186554215601687 = 144137382776465280020280387072 := by
  rw [← show ((([(7, 1), (19, 1), (337, 1), (367, 1), (35159, 1), (308679900701260499, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_19, prime_oneHundredFiftyOneES_337, prime_oneHundredFiftyOneES_367, prime_oneHundredFiftyOneES_35159, prime_oneHundredFiftyOneES_308679900701260499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601688 : Nat.totient 178522299499526186554215601688 = 88377375989581271947424889600 := by
  rw [← show ((([(2, 3), (101, 1), (312230232239, 1), (707629874244649, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_101, prime_oneHundredFiftyOneES_312230232239, prime_oneHundredFiftyOneES_707629874244649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601689 : Nat.totient 178522299499526186554215601689 = 118117061010040284912957766800 := by
  rw [← show ((([(3, 1), (191, 1), (431, 1), (722870630416403212441603, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_191, prime_oneHundredFiftyOneES_431, prime_oneHundredFiftyOneES_722870630416403212441603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601690 : Nat.totient 178522299499526186554215601690 = 71408906217707060837020992960 := by
  rw [← show ((([(2, 1), (5, 1), (5259167, 1), (19259561141, 1), (176249999227, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_5259167, prime_oneHundredFiftyOneES_19259561141, prime_oneHundredFiftyOneES_176249999227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601691 : Nat.totient 178522299499526186554215601691 = 172288438459899600699250790400 := by
  rw [← show ((([(29, 1), (2221, 1), (749893, 1), (2091361, 1), (1767329843863, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_29, prime_oneHundredFiftyOneES_2221, prime_oneHundredFiftyOneES_749893, prime_oneHundredFiftyOneES_2091361, prime_oneHundredFiftyOneES_1767329843863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601692 : Nat.totient 178522299499526186554215601692 = 52884353474869333662056448000 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (61, 1), (163, 1), (2739761, 1), (49646475480224897, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_11, prime_oneHundredFiftyOneES_61, prime_oneHundredFiftyOneES_163, prime_oneHundredFiftyOneES_2739761, prime_oneHundredFiftyOneES_49646475480224897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601693 : Nat.totient 178522299499526186554215601693 = 178109754802710071372946383040 := by
  rw [← show ((([(443, 1), (19231, 1), (598229, 1), (35028328659639349, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_443, prime_oneHundredFiftyOneES_19231, prime_oneHundredFiftyOneES_598229, prime_oneHundredFiftyOneES_35028328659639349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601694 : Nat.totient 178522299499526186554215601694 = 76478618975708289497201932032 := by
  rw [← show ((([(2, 1), (7, 1), (2473, 1), (5156325443346028148408977, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_2473, prime_oneHundredFiftyOneES_5156325443346028148408977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601695 : Nat.totient 178522299499526186554215601695 = 94718567195603531104412832768 := by
  rw [← show ((([(3, 2), (5, 1), (193, 1), (20555244617101460743145147, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_193, prime_oneHundredFiftyOneES_20555244617101460743145147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601696 : Nat.totient 178522299499526186554215601696 = 89210055788830200836765982528 := by
  rw [← show ((([(2, 5), (1747, 1), (3193372558305777521361899, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_1747, prime_oneHundredFiftyOneES_3193372558305777521361899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601697 : Nat.totient 178522299499526186554215601697 = 164780284183697032080036206400 := by
  rw [← show ((([(13, 2), (17291, 1), (460136431, 1), (132769719345253, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_13, prime_oneHundredFiftyOneES_17291, prime_oneHundredFiftyOneES_460136431, prime_oneHundredFiftyOneES_132769719345253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601698 : Nat.totient 178522299499526186554215601698 = 55979302573720998064875110400 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (2081, 1), (72973, 1), (4403543, 1), (2617313696161, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_17, prime_oneHundredFiftyOneES_2081, prime_oneHundredFiftyOneES_72973, prime_oneHundredFiftyOneES_4403543, prime_oneHundredFiftyOneES_2617313696161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601699 : Nat.totient 178522299499526186554215601699 = 170539554231657549200413898208 := by
  rw [← show ((([(23, 1), (773, 1), (198779948347, 1), (50514094095523, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_23, prime_oneHundredFiftyOneES_773, prime_oneHundredFiftyOneES_198779948347, prime_oneHundredFiftyOneES_50514094095523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601700 : Nat.totient 178522299499526186554215601700 = 71389478220774316038886832640 := by
  rw [← show ((([(2, 2), (5, 2), (3673, 1), (486039475903964569981529, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_2, prime_oneHundredFiftyOneES_5, prime_oneHundredFiftyOneES_3673, prime_oneHundredFiftyOneES_486039475903964569981529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyOneES_178522299499526186554215601701 : Nat.totient 178522299499526186554215601701 = 101777147322725585735956629504 := by
  rw [← show ((([(3, 1), (7, 1), (433, 1), (19632937369352929347213857, 1)] : List FactorBlock).map factorBlockValue).prod) = 178522299499526186554215601701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyOneES_3, prime_oneHundredFiftyOneES_7, prime_oneHundredFiftyOneES_433, prime_oneHundredFiftyOneES_19632937369352929347213857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFiftyOneES : certifiedKill 1 178522299499526186554215601599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFiftyOneES_178522299499526186554215601600, phi_oneHundredFiftyOneES_178522299499526186554215601601, phi_oneHundredFiftyOneES_178522299499526186554215601602,
    phi_oneHundredFiftyOneES_178522299499526186554215601603, phi_oneHundredFiftyOneES_178522299499526186554215601604, phi_oneHundredFiftyOneES_178522299499526186554215601605,
    phi_oneHundredFiftyOneES_178522299499526186554215601606, phi_oneHundredFiftyOneES_178522299499526186554215601607, phi_oneHundredFiftyOneES_178522299499526186554215601608,
    phi_oneHundredFiftyOneES_178522299499526186554215601609, phi_oneHundredFiftyOneES_178522299499526186554215601610, phi_oneHundredFiftyOneES_178522299499526186554215601611,
    phi_oneHundredFiftyOneES_178522299499526186554215601612, phi_oneHundredFiftyOneES_178522299499526186554215601613, phi_oneHundredFiftyOneES_178522299499526186554215601614,
    phi_oneHundredFiftyOneES_178522299499526186554215601615, phi_oneHundredFiftyOneES_178522299499526186554215601616, phi_oneHundredFiftyOneES_178522299499526186554215601617,
    phi_oneHundredFiftyOneES_178522299499526186554215601618, phi_oneHundredFiftyOneES_178522299499526186554215601619, phi_oneHundredFiftyOneES_178522299499526186554215601620,
    phi_oneHundredFiftyOneES_178522299499526186554215601621, phi_oneHundredFiftyOneES_178522299499526186554215601622, phi_oneHundredFiftyOneES_178522299499526186554215601623,
    phi_oneHundredFiftyOneES_178522299499526186554215601624, phi_oneHundredFiftyOneES_178522299499526186554215601625, phi_oneHundredFiftyOneES_178522299499526186554215601626,
    phi_oneHundredFiftyOneES_178522299499526186554215601627, phi_oneHundredFiftyOneES_178522299499526186554215601628, phi_oneHundredFiftyOneES_178522299499526186554215601629,
    phi_oneHundredFiftyOneES_178522299499526186554215601630, phi_oneHundredFiftyOneES_178522299499526186554215601631, phi_oneHundredFiftyOneES_178522299499526186554215601632,
    phi_oneHundredFiftyOneES_178522299499526186554215601633, phi_oneHundredFiftyOneES_178522299499526186554215601634, phi_oneHundredFiftyOneES_178522299499526186554215601635,
    phi_oneHundredFiftyOneES_178522299499526186554215601636, phi_oneHundredFiftyOneES_178522299499526186554215601637, phi_oneHundredFiftyOneES_178522299499526186554215601638,
    phi_oneHundredFiftyOneES_178522299499526186554215601639, phi_oneHundredFiftyOneES_178522299499526186554215601640, phi_oneHundredFiftyOneES_178522299499526186554215601641,
    phi_oneHundredFiftyOneES_178522299499526186554215601642, phi_oneHundredFiftyOneES_178522299499526186554215601643, phi_oneHundredFiftyOneES_178522299499526186554215601644,
    phi_oneHundredFiftyOneES_178522299499526186554215601645, phi_oneHundredFiftyOneES_178522299499526186554215601646, phi_oneHundredFiftyOneES_178522299499526186554215601647,
    phi_oneHundredFiftyOneES_178522299499526186554215601648, phi_oneHundredFiftyOneES_178522299499526186554215601649, phi_oneHundredFiftyOneES_178522299499526186554215601650,
    phi_oneHundredFiftyOneES_178522299499526186554215601651, phi_oneHundredFiftyOneES_178522299499526186554215601652, phi_oneHundredFiftyOneES_178522299499526186554215601653,
    phi_oneHundredFiftyOneES_178522299499526186554215601654, phi_oneHundredFiftyOneES_178522299499526186554215601655, phi_oneHundredFiftyOneES_178522299499526186554215601656,
    phi_oneHundredFiftyOneES_178522299499526186554215601657, phi_oneHundredFiftyOneES_178522299499526186554215601658, phi_oneHundredFiftyOneES_178522299499526186554215601659,
    phi_oneHundredFiftyOneES_178522299499526186554215601660, phi_oneHundredFiftyOneES_178522299499526186554215601661, phi_oneHundredFiftyOneES_178522299499526186554215601662,
    phi_oneHundredFiftyOneES_178522299499526186554215601663, phi_oneHundredFiftyOneES_178522299499526186554215601664, phi_oneHundredFiftyOneES_178522299499526186554215601665,
    phi_oneHundredFiftyOneES_178522299499526186554215601666, phi_oneHundredFiftyOneES_178522299499526186554215601667, phi_oneHundredFiftyOneES_178522299499526186554215601668,
    phi_oneHundredFiftyOneES_178522299499526186554215601669, phi_oneHundredFiftyOneES_178522299499526186554215601670, phi_oneHundredFiftyOneES_178522299499526186554215601671,
    phi_oneHundredFiftyOneES_178522299499526186554215601672, phi_oneHundredFiftyOneES_178522299499526186554215601673, phi_oneHundredFiftyOneES_178522299499526186554215601674,
    phi_oneHundredFiftyOneES_178522299499526186554215601675, phi_oneHundredFiftyOneES_178522299499526186554215601676, phi_oneHundredFiftyOneES_178522299499526186554215601677,
    phi_oneHundredFiftyOneES_178522299499526186554215601678, phi_oneHundredFiftyOneES_178522299499526186554215601679, phi_oneHundredFiftyOneES_178522299499526186554215601680,
    phi_oneHundredFiftyOneES_178522299499526186554215601681, phi_oneHundredFiftyOneES_178522299499526186554215601682, phi_oneHundredFiftyOneES_178522299499526186554215601683,
    phi_oneHundredFiftyOneES_178522299499526186554215601684, phi_oneHundredFiftyOneES_178522299499526186554215601685, phi_oneHundredFiftyOneES_178522299499526186554215601686,
    phi_oneHundredFiftyOneES_178522299499526186554215601687, phi_oneHundredFiftyOneES_178522299499526186554215601688, phi_oneHundredFiftyOneES_178522299499526186554215601689,
    phi_oneHundredFiftyOneES_178522299499526186554215601690, phi_oneHundredFiftyOneES_178522299499526186554215601691, phi_oneHundredFiftyOneES_178522299499526186554215601692,
    phi_oneHundredFiftyOneES_178522299499526186554215601693, phi_oneHundredFiftyOneES_178522299499526186554215601694, phi_oneHundredFiftyOneES_178522299499526186554215601695,
    phi_oneHundredFiftyOneES_178522299499526186554215601696, phi_oneHundredFiftyOneES_178522299499526186554215601697, phi_oneHundredFiftyOneES_178522299499526186554215601698,
    phi_oneHundredFiftyOneES_178522299499526186554215601699, phi_oneHundredFiftyOneES_178522299499526186554215601700, phi_oneHundredFiftyOneES_178522299499526186554215601701
    ]

end TotientTailPeriodKiller
end Erdos249257
