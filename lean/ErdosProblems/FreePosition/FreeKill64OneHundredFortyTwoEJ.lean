import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFortyTwoEJFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFortyTwoEJFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFortyTwoEJFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFortyTwoEJFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFortyTwoEJFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFortyTwoEJFastPow a n * oneHundredFortyTwoEJFastPow a n * a else oneHundredFortyTwoEJFastPow a n * oneHundredFortyTwoEJFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFortyTwoEJ_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1777 : Nat.Prime 1777 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2351 : Nat.Prime 2351 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2383 : Nat.Prime 2383 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2531 : Nat.Prime 2531 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2539 : Nat.Prime 2539 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2671 : Nat.Prime 2671 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2683 : Nat.Prime 2683 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2707 : Nat.Prime 2707 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2953 : Nat.Prime 2953 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3023 : Nat.Prime 3023 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3061 : Nat.Prime 3061 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3119 : Nat.Prime 3119 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3167 : Nat.Prime 3167 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3181 : Nat.Prime 3181 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3271 : Nat.Prime 3271 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3527 : Nat.Prime 3527 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3803 : Nat.Prime 3803 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_4129 : Nat.Prime 4129 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_4157 : Nat.Prime 4157 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_4243 : Nat.Prime 4243 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_4397 : Nat.Prime 4397 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6151 : Nat.Prime 6151 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6311 : Nat.Prime 6311 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6367 : Nat.Prime 6367 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6571 : Nat.Prime 6571 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6871 : Nat.Prime 6871 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6959 : Nat.Prime 6959 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6961 : Nat.Prime 6961 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6997 : Nat.Prime 6997 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_7229 : Nat.Prime 7229 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_7481 : Nat.Prime 7481 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_7603 : Nat.Prime 7603 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_7607 : Nat.Prime 7607 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_8231 : Nat.Prime 8231 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_8887 : Nat.Prime 8887 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_8969 : Nat.Prime 8969 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_9043 : Nat.Prime 9043 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_9151 : Nat.Prime 9151 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_9227 : Nat.Prime 9227 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_9311 : Nat.Prime 9311 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_9733 : Nat.Prime 9733 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_10133 : Nat.Prime 10133 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_10159 : Nat.Prime 10159 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_10259 : Nat.Prime 10259 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_10781 : Nat.Prime 10781 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_11467 : Nat.Prime 11467 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_11827 : Nat.Prime 11827 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_12203 : Nat.Prime 12203 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_12253 : Nat.Prime 12253 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_12451 : Nat.Prime 12451 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_13043 : Nat.Prime 13043 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_13691 : Nat.Prime 13691 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_13757 : Nat.Prime 13757 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_13759 : Nat.Prime 13759 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_13931 : Nat.Prime 13931 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_14051 : Nat.Prime 14051 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_14303 : Nat.Prime 14303 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_14543 : Nat.Prime 14543 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_14629 : Nat.Prime 14629 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_14923 : Nat.Prime 14923 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_15629 : Nat.Prime 15629 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_16141 : Nat.Prime 16141 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_16451 : Nat.Prime 16451 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_16691 : Nat.Prime 16691 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_17189 : Nat.Prime 17189 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_17519 : Nat.Prime 17519 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_18169 : Nat.Prime 18169 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_19541 : Nat.Prime 19541 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_19891 : Nat.Prime 19891 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_20353 : Nat.Prime 20353 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_20389 : Nat.Prime 20389 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_20399 : Nat.Prime 20399 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_22639 : Nat.Prime 22639 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_22643 : Nat.Prime 22643 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_22859 : Nat.Prime 22859 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_23201 : Nat.Prime 23201 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_23899 : Nat.Prime 23899 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_24133 : Nat.Prime 24133 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_24733 : Nat.Prime 24733 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_25097 : Nat.Prime 25097 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_25339 : Nat.Prime 25339 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_25609 : Nat.Prime 25609 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_26357 : Nat.Prime 26357 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_26497 : Nat.Prime 26497 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_27077 : Nat.Prime 27077 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_27431 : Nat.Prime 27431 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_28087 : Nat.Prime 28087 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_28729 : Nat.Prime 28729 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_29209 : Nat.Prime 29209 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_30013 : Nat.Prime 30013 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_30449 : Nat.Prime 30449 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_30949 : Nat.Prime 30949 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_31601 : Nat.Prime 31601 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_31817 : Nat.Prime 31817 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_31873 : Nat.Prime 31873 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_32321 : Nat.Prime 32321 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_34543 : Nat.Prime 34543 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_34679 : Nat.Prime 34679 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_37907 : Nat.Prime 37907 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_38287 : Nat.Prime 38287 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_38371 : Nat.Prime 38371 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_39107 : Nat.Prime 39107 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_40099 : Nat.Prime 40099 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_40637 : Nat.Prime 40637 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_41257 : Nat.Prime 41257 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_41687 : Nat.Prime 41687 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_45833 : Nat.Prime 45833 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_45869 : Nat.Prime 45869 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_46829 : Nat.Prime 46829 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_47251 : Nat.Prime 47251 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_50651 : Nat.Prime 50651 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_51577 : Nat.Prime 51577 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_52289 : Nat.Prime 52289 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_53087 : Nat.Prime 53087 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_53093 : Nat.Prime 53093 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_57427 : Nat.Prime 57427 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_58271 : Nat.Prime 58271 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_58427 : Nat.Prime 58427 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_58901 : Nat.Prime 58901 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_59447 : Nat.Prime 59447 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_60397 : Nat.Prime 60397 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_63929 : Nat.Prime 63929 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_64399 : Nat.Prime 64399 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_65963 : Nat.Prime 65963 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_69931 : Nat.Prime 69931 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_71563 : Nat.Prime 71563 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_71917 : Nat.Prime 71917 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_72559 : Nat.Prime 72559 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_72767 : Nat.Prime 72767 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_80173 : Nat.Prime 80173 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_82037 : Nat.Prime 82037 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_82883 : Nat.Prime 82883 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_86209 : Nat.Prime 86209 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_95581 : Nat.Prime 95581 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_97151 : Nat.Prime 97151 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_98347 : Nat.Prime 98347 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_100361 : Nat.Prime 100361 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_103967 : Nat.Prime 103967 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_105863 : Nat.Prime 105863 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_106349 : Nat.Prime 106349 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_110221 : Nat.Prime 110221 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_110233 : Nat.Prime 110233 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_111653 : Nat.Prime 111653 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_114199 : Nat.Prime 114199 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_117773 : Nat.Prime 117773 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_121711 : Nat.Prime 121711 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_128389 : Nat.Prime 128389 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_132859 : Nat.Prime 132859 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_138371 : Nat.Prime 138371 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_141497 : Nat.Prime 141497 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_144583 : Nat.Prime 144583 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_145121 : Nat.Prime 145121 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_150211 : Nat.Prime 150211 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_150589 : Nat.Prime 150589 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_186761 : Nat.Prime 186761 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_188633 : Nat.Prime 188633 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_199657 : Nat.Prime 199657 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_214177 : Nat.Prime 214177 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_217733 : Nat.Prime 217733 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_225157 : Nat.Prime 225157 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_243487 : Nat.Prime 243487 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_243863 : Nat.Prime 243863 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_248779 : Nat.Prime 248779 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_249859 : Nat.Prime 249859 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_257519 : Nat.Prime 257519 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_260893 : Nat.Prime 260893 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_269683 : Nat.Prime 269683 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_269891 : Nat.Prime 269891 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_289031 : Nat.Prime 289031 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_292241 : Nat.Prime 292241 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_311473 : Nat.Prime 311473 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_325697 : Nat.Prime 325697 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_329081 : Nat.Prime 329081 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_346091 : Nat.Prime 346091 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_357431 : Nat.Prime 357431 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_362137 : Nat.Prime 362137 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_392809 : Nat.Prime 392809 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_406729 : Nat.Prime 406729 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_437287 : Nat.Prime 437287 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_492389 : Nat.Prime 492389 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_513307 : Nat.Prime 513307 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_532733 : Nat.Prime 532733 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_536233 : Nat.Prime 536233 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_541889 : Nat.Prime 541889 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_564989 : Nat.Prime 564989 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_660493 : Nat.Prime 660493 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_670223 : Nat.Prime 670223 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_698903 : Nat.Prime 698903 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_731729 : Nat.Prime 731729 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_771091 : Nat.Prime 771091 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_803273 : Nat.Prime 803273 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_816917 : Nat.Prime 816917 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_820921 : Nat.Prime 820921 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_830989 : Nat.Prime 830989 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_861659 : Nat.Prime 861659 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_885947 : Nat.Prime 885947 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_925447 : Nat.Prime 925447 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_931913 : Nat.Prime 931913 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_967721 : Nat.Prime 967721 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_986137 : Nat.Prime 986137 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1038463 : Nat.Prime 1038463 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1207529 : Nat.Prime 1207529 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1207757 : Nat.Prime 1207757 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1278493 : Nat.Prime 1278493 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1359361 : Nat.Prime 1359361 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1608017 : Nat.Prime 1608017 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1627649 : Nat.Prime 1627649 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1669861 : Nat.Prime 1669861 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1707851 : Nat.Prime 1707851 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1769111 : Nat.Prime 1769111 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1783799 : Nat.Prime 1783799 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1963711 : Nat.Prime 1963711 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_1998947 : Nat.Prime 1998947 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2042347 : Nat.Prime 2042347 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2063807 : Nat.Prime 2063807 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2105611 : Nat.Prime 2105611 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2130133 : Nat.Prime 2130133 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2330837 : Nat.Prime 2330837 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2361701 : Nat.Prime 2361701 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2467277 : Nat.Prime 2467277 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2561749 : Nat.Prime 2561749 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2580443 : Nat.Prime 2580443 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2806651 : Nat.Prime 2806651 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2817511 : Nat.Prime 2817511 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_2983543 : Nat.Prime 2983543 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3039727 : Nat.Prime 3039727 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3188657 : Nat.Prime 3188657 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3192017 : Nat.Prime 3192017 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3414349 : Nat.Prime 3414349 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3443347 : Nat.Prime 3443347 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3460091 : Nat.Prime 3460091 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3503909 : Nat.Prime 3503909 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3517247 : Nat.Prime 3517247 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3544657 : Nat.Prime 3544657 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3831577 : Nat.Prime 3831577 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_3883967 : Nat.Prime 3883967 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_4209223 : Nat.Prime 4209223 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_4398133 : Nat.Prime 4398133 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_5094899 : Nat.Prime 5094899 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_5161411 : Nat.Prime 5161411 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_5818277 : Nat.Prime 5818277 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6005477 : Nat.Prime 6005477 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6019289 : Nat.Prime 6019289 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6030851 : Nat.Prime 6030851 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6460687 : Nat.Prime 6460687 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6470839 : Nat.Prime 6470839 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_6655543 : Nat.Prime 6655543 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_7046749 : Nat.Prime 7046749 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_7208899 : Nat.Prime 7208899 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_7268119 : Nat.Prime 7268119 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_8466079 : Nat.Prime 8466079 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_8497033 : Nat.Prime 8497033 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_8633489 : Nat.Prime 8633489 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_8885347 : Nat.Prime 8885347 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_9057431 : Nat.Prime 9057431 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_10559947 : Nat.Prime 10559947 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_11144521 : Nat.Prime 11144521 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_11269631 : Nat.Prime 11269631 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_11338279 : Nat.Prime 11338279 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_12343481 : Nat.Prime 12343481 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_12701209 : Nat.Prime 12701209 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_12762437 : Nat.Prime 12762437 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_12768907 : Nat.Prime 12768907 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_14936899 : Nat.Prime 14936899 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_15049621 : Nat.Prime 15049621 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_16257431 : Nat.Prime 16257431 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_16439957 : Nat.Prime 16439957 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_18631853 : Nat.Prime 18631853 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_18842893 : Nat.Prime 18842893 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_19478729 : Nat.Prime 19478729 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_20437117 : Nat.Prime 20437117 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_20840311 : Nat.Prime 20840311 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_20984779 : Nat.Prime 20984779 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_22594093 : Nat.Prime 22594093 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_23170471 : Nat.Prime 23170471 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_26262287 : Nat.Prime 26262287 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_26480309 : Nat.Prime 26480309 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_28133789 : Nat.Prime 28133789 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_29223839 : Nat.Prime 29223839 := by norm_num

private theorem prime_oneHundredFortyTwoEJ_30967073 : Nat.Prime 30967073 := by
  apply lucas_primality 30967073 (3 : ZMod 30967073)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (967721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (967721, 1)] : List FactorBlock).map factorBlockValue).prod) = 30967073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_967721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 30967073) ^ 15483536 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30967073) ^ 32 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_31904701 : Nat.Prime 31904701 := by
  apply lucas_primality 31904701 (7 : ZMod 31904701)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (106349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (106349, 1)] : List FactorBlock).map factorBlockValue).prod) = 31904701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_106349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 31904701) ^ 15952350 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 31904701) ^ 10634900 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 31904701) ^ 6380940 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 31904701) ^ 300 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_33984161 : Nat.Prime 33984161 := by
  apply lucas_primality 33984161 (3 : ZMod 33984161)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (19, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (19, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) = 33984161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_1597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33984161) ^ 16992080 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33984161) ^ 6796832 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33984161) ^ 4854880 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33984161) ^ 1788640 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33984161) ^ 21280 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_35625613 : Nat.Prime 35625613 := by
  apply lucas_primality 35625613 (2 : ZMod 35625613)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (269891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (269891, 1)] : List FactorBlock).map factorBlockValue).prod) = 35625613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_269891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35625613) ^ 17812806 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 35625613) ^ 11875204 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 35625613) ^ 3238692 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 35625613) ^ 132 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_36465859 : Nat.Prime 36465859 := by
  apply lucas_primality 36465859 (3 : ZMod 36465859)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (13, 1), (31, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (13, 1), (31, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) = 36465859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36465859) ^ 18232929 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 36465859) ^ 12155286 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 36465859) ^ 3315078 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 36465859) ^ 2805066 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 36465859) ^ 1176318 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 36465859) ^ 79794 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_39043261 : Nat.Prime 39043261 := by
  apply lucas_primality 39043261 (6 : ZMod 39043261)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (31, 1), (6997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (31, 1), (6997, 1)] : List FactorBlock).map factorBlockValue).prod) = 39043261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_6997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 39043261) ^ 19521630 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 39043261) ^ 13014420 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 39043261) ^ 7808652 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 39043261) ^ 1259460 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 39043261) ^ 5580 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_40491491 : Nat.Prime 40491491 := by
  apply lucas_primality 40491491 (2 : ZMod 40491491)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (311473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (311473, 1)] : List FactorBlock).map factorBlockValue).prod) = 40491491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_311473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40491491) ^ 20245745 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40491491) ^ 8098298 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40491491) ^ 3114730 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40491491) ^ 130 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_43507003 : Nat.Prime 43507003 := by
  apply lucas_primality 43507003 (2 : ZMod 43507003)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (11, 2), (1223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (11, 2), (1223, 1)] : List FactorBlock).map factorBlockValue).prod) = 43507003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_1223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43507003) ^ 21753501 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 43507003) ^ 14502334 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 43507003) ^ 6215286 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 43507003) ^ 3955182 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 43507003) ^ 35574 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_44221633 : Nat.Prime 44221633 := by
  apply lucas_primality 44221633 (10 : ZMod 44221633)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (13, 1), (2531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (13, 1), (2531, 1)] : List FactorBlock).map factorBlockValue).prod) = 44221633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_2531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 44221633) ^ 22110816 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 44221633) ^ 14740544 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 44221633) ^ 6317376 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 44221633) ^ 3401664 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 44221633) ^ 17472 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_44404127 : Nat.Prime 44404127 := by
  apply lucas_primality 44404127 (5 : ZMod 44404127)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1707851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1707851, 1)] : List FactorBlock).map factorBlockValue).prod) = 44404127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_1707851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 44404127) ^ 22202063 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44404127) ^ 3415702 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 44404127) ^ 26 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_44432501 : Nat.Prime 44432501 := by
  apply lucas_primality 44432501 (2 : ZMod 44432501)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 4), (7, 1), (2539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 4), (7, 1), (2539, 1)] : List FactorBlock).map factorBlockValue).prod) = 44432501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_2539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 44432501) ^ 22216250 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44432501) ^ 8886500 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44432501) ^ 6347500 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 44432501) ^ 17500 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_44688239 : Nat.Prime 44688239 := by
  apply lucas_primality 44688239 (7 : ZMod 44688239)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3192017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3192017, 1)] : List FactorBlock).map factorBlockValue).prod) = 44688239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_3192017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 44688239) ^ 22344119 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 44688239) ^ 6384034 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 44688239) ^ 14 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_51210391 : Nat.Prime 51210391 := by
  apply lucas_primality 51210391 (3 : ZMod 51210391)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (11, 1), (3167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (11, 1), (3167, 1)] : List FactorBlock).map factorBlockValue).prod) = 51210391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_3167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51210391) ^ 25605195 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51210391) ^ 17070130 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51210391) ^ 10242078 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51210391) ^ 7315770 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51210391) ^ 4655490 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 51210391) ^ 16170 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_53579969 : Nat.Prime 53579969 := by
  apply lucas_primality 53579969 (3 : ZMod 53579969)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (64399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (64399, 1)] : List FactorBlock).map factorBlockValue).prod) = 53579969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_64399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53579969) ^ 26789984 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 53579969) ^ 4121536 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 53579969) ^ 832 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_56419273 : Nat.Prime 56419273 := by
  apply lucas_primality 56419273 (5 : ZMod 56419273)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (13, 1), (79, 1), (109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (13, 1), (79, 1), (109, 1)] : List FactorBlock).map factorBlockValue).prod) = 56419273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_79
      · exact prime_oneHundredFortyTwoEJ_109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 56419273) ^ 28209636 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 56419273) ^ 18806424 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 56419273) ^ 8059896 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 56419273) ^ 4339944 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 56419273) ^ 714168 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 56419273) ^ 517608 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_1811
      · exact prime_oneHundredFortyTwoEJ_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_65146979 : Nat.Prime 65146979 := by
  apply lucas_primality 65146979 (2 : ZMod 65146979)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (43, 1), (58271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (43, 1), (58271, 1)] : List FactorBlock).map factorBlockValue).prod) = 65146979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_43
      · exact prime_oneHundredFortyTwoEJ_58271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 65146979) ^ 32573489 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 65146979) ^ 5011306 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 65146979) ^ 1515046 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 65146979) ^ 1118 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_67968323 : Nat.Prime 67968323 := by
  apply lucas_primality 67968323 (2 : ZMod 67968323)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (33984161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (33984161, 1)] : List FactorBlock).map factorBlockValue).prod) = 67968323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_33984161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 67968323) ^ 33984161 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 67968323) ^ 2 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_68495381 : Nat.Prime 68495381 := by
  apply lucas_primality 68495381 (2 : ZMod 68495381)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (19, 1), (23, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (19, 1), (23, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) = 68495381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68495381) ^ 34247690 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68495381) ^ 13699076 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68495381) ^ 4029140 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68495381) ^ 3605020 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68495381) ^ 2978060 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68495381) ^ 148580 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_70990649 : Nat.Prime 70990649 := by
  apply lucas_primality 70990649 (3 : ZMod 70990649)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (107, 1), (239, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (107, 1), (239, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) = 70990649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_107
      · exact prime_oneHundredFortyTwoEJ_239
      · exact prime_oneHundredFortyTwoEJ_347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 70990649) ^ 35495324 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 70990649) ^ 663464 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 70990649) ^ 297032 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 70990649) ^ 204584 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_77224201 : Nat.Prime 77224201 := by
  apply lucas_primality 77224201 (11 : ZMod 77224201)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (17, 1), (67, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (17, 1), (67, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 77224201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_67
      · exact prime_oneHundredFortyTwoEJ_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 77224201) ^ 38612100 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 77224201) ^ 25741400 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 77224201) ^ 15444840 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 77224201) ^ 4542600 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 77224201) ^ 1152600 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 77224201) ^ 683400 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_78588361 : Nat.Prime 78588361 := by
  apply lucas_primality 78588361 (14 : ZMod 78588361)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (72767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (72767, 1)] : List FactorBlock).map factorBlockValue).prod) = 78588361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_72767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 78588361) ^ 39294180 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 78588361) ^ 26196120 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 78588361) ^ 15717672 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 78588361) ^ 1080 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_95033579 : Nat.Prime 95033579 := by
  apply lucas_primality 95033579 (2 : ZMod 95033579)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (248779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (248779, 1)] : List FactorBlock).map factorBlockValue).prod) = 95033579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_191
      · exact prime_oneHundredFortyTwoEJ_248779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 95033579) ^ 47516789 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 95033579) ^ 497558 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 95033579) ^ 382 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_100165633 : Nat.Prime 100165633 := by
  apply lucas_primality 100165633 (10 : ZMod 100165633)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (3, 1), (7, 1), (17, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (3, 1), (7, 1), (17, 1), (137, 1)] : List FactorBlock).map factorBlockValue).prod) = 100165633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 100165633) ^ 50082816 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 100165633) ^ 33388544 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 100165633) ^ 14309376 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 100165633) ^ 5892096 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 100165633) ^ 731136 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_104714629 : Nat.Prime 104714629 := by
  apply lucas_primality 104714629 (2 : ZMod 104714629)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (513307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (513307, 1)] : List FactorBlock).map factorBlockValue).prod) = 104714629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_513307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 104714629) ^ 52357314 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 104714629) ^ 34904876 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 104714629) ^ 6159684 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 104714629) ^ 204 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_109345157 : Nat.Prime 109345157 := by
  apply lucas_primality 109345157 (2 : ZMod 109345157)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (1608017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (1608017, 1)] : List FactorBlock).map factorBlockValue).prod) = 109345157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_1608017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 109345157) ^ 54672578 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 109345157) ^ 6432068 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 109345157) ^ 68 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_111378697 : Nat.Prime 111378697 := by
  apply lucas_primality 111378697 (7 : ZMod 111378697)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 1), (17, 1), (23, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 1), (17, 1), (23, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) = 111378697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_83
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 111378697) ^ 55689348 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 111378697) ^ 37126232 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 111378697) ^ 10125336 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 111378697) ^ 8567592 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 111378697) ^ 6551688 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 111378697) ^ 4842552 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 111378697) ^ 1341912 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_111445211 : Nat.Prime 111445211 := by
  apply lucas_primality 111445211 (2 : ZMod 111445211)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11144521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11144521, 1)] : List FactorBlock).map factorBlockValue).prod) = 111445211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_11144521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 111445211) ^ 55722605 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 111445211) ^ 22289042 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 111445211) ^ 10 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_116895659 : Nat.Prime 116895659 := by
  apply lucas_primality 116895659 (2 : ZMod 116895659)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (167, 1), (31817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (167, 1), (31817, 1)] : List FactorBlock).map factorBlockValue).prod) = 116895659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_167
      · exact prime_oneHundredFortyTwoEJ_31817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 116895659) ^ 58447829 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 116895659) ^ 10626878 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 116895659) ^ 699974 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 116895659) ^ 3674 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_130293959 : Nat.Prime 130293959 := by
  apply lucas_primality 130293959 (11 : ZMod 130293959)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (65146979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (65146979, 1)] : List FactorBlock).map factorBlockValue).prod) = 130293959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_65146979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 130293959) ^ 65146979 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 130293959) ^ 2 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_136211263 : Nat.Prime 136211263 := by
  apply lucas_primality 136211263 (3 : ZMod 136211263)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (2063807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (2063807, 1)] : List FactorBlock).map factorBlockValue).prod) = 136211263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_2063807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 136211263) ^ 68105631 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 136211263) ^ 45403754 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 136211263) ^ 12382842 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 136211263) ^ 66 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_150359813 : Nat.Prime 150359813 := by
  apply lucas_primality 150359813 (2 : ZMod 150359813)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (103, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (103, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) = 150359813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_83
      · exact prime_oneHundredFortyTwoEJ_103
      · exact prime_oneHundredFortyTwoEJ_4397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 150359813) ^ 75179906 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 150359813) ^ 1811564 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 150359813) ^ 1459804 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 150359813) ^ 34196 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_157573723 : Nat.Prime 157573723 := by
  apply lucas_primality 157573723 (2 : ZMod 157573723)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (26262287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (26262287, 1)] : List FactorBlock).map factorBlockValue).prod) = 157573723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_26262287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 157573723) ^ 78786861 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 157573723) ^ 52524574 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 157573723) ^ 6 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_184721587 : Nat.Prime 184721587 := by
  apply lucas_primality 184721587 (2 : ZMod 184721587)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (4398133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (4398133, 1)] : List FactorBlock).map factorBlockValue).prod) = 184721587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_4398133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 184721587) ^ 92360793 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 184721587) ^ 61573862 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 184721587) ^ 26388798 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 184721587) ^ 42 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_192772751 : Nat.Prime 192772751 := by
  apply lucas_primality 192772751 (13 : ZMod 192772751)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (771091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (771091, 1)] : List FactorBlock).map factorBlockValue).prod) = 192772751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_771091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 192772751) ^ 96386375 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 192772751) ^ 38554550 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 192772751) ^ 250 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_203185897 : Nat.Prime 203185897 := by
  apply lucas_primality 203185897 (5 : ZMod 203185897)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8466079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8466079, 1)] : List FactorBlock).map factorBlockValue).prod) = 203185897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_8466079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 203185897) ^ 101592948 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 203185897) ^ 67728632 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 203185897) ^ 24 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_233791319 : Nat.Prime 233791319 := by
  apply lucas_primality 233791319 (11 : ZMod 233791319)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (116895659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (116895659, 1)] : List FactorBlock).map factorBlockValue).prod) = 233791319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_116895659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 233791319) ^ 116895659 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 233791319) ^ 2 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_237418427 : Nat.Prime 237418427 := by
  apply lucas_primality 237418427 (2 : ZMod 237418427)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (346091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (346091, 1)] : List FactorBlock).map factorBlockValue).prod) = 237418427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_346091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 237418427) ^ 118709213 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237418427) ^ 33916918 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237418427) ^ 686 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_278710139 : Nat.Prime 278710139 := by
  apply lucas_primality 278710139 (2 : ZMod 278710139)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (17, 1), (23899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (17, 1), (23899, 1)] : List FactorBlock).map factorBlockValue).prod) = 278710139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_23899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 278710139) ^ 139355069 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 278710139) ^ 39815734 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 278710139) ^ 16394714 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 278710139) ^ 11662 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_300260509 : Nat.Prime 300260509 := by
  apply lucas_primality 300260509 (6 : ZMod 300260509)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (997, 1), (25097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (997, 1), (25097, 1)] : List FactorBlock).map factorBlockValue).prod) = 300260509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_997
      · exact prime_oneHundredFortyTwoEJ_25097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 300260509) ^ 150130254 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 300260509) ^ 100086836 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 300260509) ^ 301164 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 300260509) ^ 11964 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_304321387 : Nat.Prime 304321387 := by
  apply lucas_primality 304321387 (3 : ZMod 304321387)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (2983543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (2983543, 1)] : List FactorBlock).map factorBlockValue).prod) = 304321387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_2983543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 304321387) ^ 152160693 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 304321387) ^ 101440462 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 304321387) ^ 17901258 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 304321387) ^ 102 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_304972181 : Nat.Prime 304972181 := by
  apply lucas_primality 304972181 (2 : ZMod 304972181)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (23, 1), (59, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (23, 1), (59, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) = 304972181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_59
      · exact prime_oneHundredFortyTwoEJ_661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 304972181) ^ 152486090 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 304972181) ^ 60994436 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 304972181) ^ 17939540 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 304972181) ^ 13259660 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 304972181) ^ 5169020 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 304972181) ^ 461380 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_317267677 : Nat.Prime 317267677 := by
  apply lucas_primality 317267677 (7 : ZMod 317267677)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (41, 1), (19541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (41, 1), (19541, 1)] : List FactorBlock).map factorBlockValue).prod) = 317267677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_41
      · exact prime_oneHundredFortyTwoEJ_19541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 317267677) ^ 158633838 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 317267677) ^ 105755892 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 317267677) ^ 28842516 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 317267677) ^ 7738236 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 317267677) ^ 16236 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_350187269 : Nat.Prime 350187269 := by
  apply lucas_primality 350187269 (2 : ZMod 350187269)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (359, 1), (243863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (359, 1), (243863, 1)] : List FactorBlock).map factorBlockValue).prod) = 350187269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_359
      · exact prime_oneHundredFortyTwoEJ_243863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 350187269) ^ 175093634 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 350187269) ^ 975452 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 350187269) ^ 1436 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_353649991 : Nat.Prime 353649991 := by
  apply lucas_primality 353649991 (3 : ZMod 353649991)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (257, 1), (45869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (257, 1), (45869, 1)] : List FactorBlock).map factorBlockValue).prod) = 353649991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_257
      · exact prime_oneHundredFortyTwoEJ_45869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 353649991) ^ 176824995 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 353649991) ^ 117883330 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 353649991) ^ 70729998 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 353649991) ^ 1376070 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 353649991) ^ 7710 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_390432611 : Nat.Prime 390432611 := by
  apply lucas_primality 390432611 (2 : ZMod 390432611)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (39043261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (39043261, 1)] : List FactorBlock).map factorBlockValue).prod) = 390432611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_39043261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 390432611) ^ 195216305 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 390432611) ^ 78086522 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 390432611) ^ 10 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_395374769 : Nat.Prime 395374769 := by
  apply lucas_primality 395374769 (3 : ZMod 395374769)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (131, 1), (188633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (131, 1), (188633, 1)] : List FactorBlock).map factorBlockValue).prod) = 395374769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_131
      · exact prime_oneHundredFortyTwoEJ_188633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 395374769) ^ 197687384 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 395374769) ^ 3018128 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 395374769) ^ 2096 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_400662533 : Nat.Prime 400662533 := by
  apply lucas_primality 400662533 (2 : ZMod 400662533)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (100165633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (100165633, 1)] : List FactorBlock).map factorBlockValue).prod) = 400662533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_100165633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 400662533) ^ 200331266 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 400662533) ^ 4 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_417120883 : Nat.Prime 417120883 := by
  apply lucas_primality 417120883 (3 : ZMod 417120883)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (107, 1), (9151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (107, 1), (9151, 1)] : List FactorBlock).map factorBlockValue).prod) = 417120883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_71
      · exact prime_oneHundredFortyTwoEJ_107
      · exact prime_oneHundredFortyTwoEJ_9151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 417120883) ^ 208560441 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 417120883) ^ 139040294 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 417120883) ^ 5874942 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 417120883) ^ 3898326 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 417120883) ^ 45582 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_443053313 : Nat.Prime 443053313 := by
  apply lucas_primality 443053313 (3 : ZMod 443053313)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (13, 1), (67, 1), (1987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (13, 1), (67, 1), (1987, 1)] : List FactorBlock).map factorBlockValue).prod) = 443053313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_67
      · exact prime_oneHundredFortyTwoEJ_1987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 443053313) ^ 221526656 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 443053313) ^ 34081024 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 443053313) ^ 6612736 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 443053313) ^ 222976 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_494355263 : Nat.Prime 494355263 := by
  apply lucas_primality 494355263 (5 : ZMod 494355263)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (43, 1), (97, 1), (3119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (43, 1), (97, 1), (3119, 1)] : List FactorBlock).map factorBlockValue).prod) = 494355263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_43
      · exact prime_oneHundredFortyTwoEJ_97
      · exact prime_oneHundredFortyTwoEJ_3119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 494355263) ^ 247177631 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 494355263) ^ 26018698 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 494355263) ^ 11496634 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 494355263) ^ 5096446 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 494355263) ^ 158498 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_497426297 : Nat.Prime 497426297 := by
  apply lucas_primality 497426297 (3 : ZMod 497426297)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (109, 1), (661, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (109, 1), (661, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) = 497426297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_109
      · exact prime_oneHundredFortyTwoEJ_661
      · exact prime_oneHundredFortyTwoEJ_863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 497426297) ^ 248713148 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 497426297) ^ 4563544 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 497426297) ^ 752536 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 497426297) ^ 576392 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_499879469 : Nat.Prime 499879469 := by
  apply lucas_primality 499879469 (2 : ZMod 499879469)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1847, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1847, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) = 499879469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_1847
      · exact prime_oneHundredFortyTwoEJ_6151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 499879469) ^ 249939734 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 499879469) ^ 45443588 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 499879469) ^ 270644 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 499879469) ^ 81268 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_514464281 : Nat.Prime 514464281 := by
  apply lucas_primality 514464281 (6 : ZMod 514464281)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (37, 1), (31601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (37, 1), (31601, 1)] : List FactorBlock).map factorBlockValue).prod) = 514464281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_37
      · exact prime_oneHundredFortyTwoEJ_31601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 514464281) ^ 257232140 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 514464281) ^ 102892856 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 514464281) ^ 46769480 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 514464281) ^ 13904440 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 514464281) ^ 16280 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_607543163 : Nat.Prime 607543163 := by
  apply lucas_primality 607543163 (2 : ZMod 607543163)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1051, 1), (289031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1051, 1), (289031, 1)] : List FactorBlock).map factorBlockValue).prod) = 607543163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_1051
      · exact prime_oneHundredFortyTwoEJ_289031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 607543163) ^ 303771581 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 607543163) ^ 578062 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 607543163) ^ 2102 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_618599459 : Nat.Prime 618599459 := by
  apply lucas_primality 618599459 (2 : ZMod 618599459)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (3188657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (3188657, 1)] : List FactorBlock).map factorBlockValue).prod) = 618599459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_97
      · exact prime_oneHundredFortyTwoEJ_3188657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 618599459) ^ 309299729 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 618599459) ^ 6377314 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 618599459) ^ 194 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_17203
      · exact prime_oneHundredFortyTwoEJ_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_734535481 : Nat.Prime 734535481 := by
  apply lucas_primality 734535481 (31 : ZMod 734535481)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 2), (53, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 2), (53, 1), (2357, 1)] : List FactorBlock).map factorBlockValue).prod) = 734535481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_53
      · exact prime_oneHundredFortyTwoEJ_2357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 734535481) ^ 367267740 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (31 : ZMod 734535481) ^ 244845160 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (31 : ZMod 734535481) ^ 146907096 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (31 : ZMod 734535481) ^ 104933640 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (31 : ZMod 734535481) ^ 13859160 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (31 : ZMod 734535481) ^ 311640 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_739415447 : Nat.Prime 739415447 := by
  apply lucas_primality 739415447 (5 : ZMod 739415447)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (1601, 1), (2999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (1601, 1), (2999, 1)] : List FactorBlock).map factorBlockValue).prod) = 739415447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_1601
      · exact prime_oneHundredFortyTwoEJ_2999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 739415447) ^ 369707723 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 739415447) ^ 105630778 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 739415447) ^ 67219586 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 739415447) ^ 461846 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 739415447) ^ 246554 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_918423551 : Nat.Prime 918423551 := by
  apply lucas_primality 918423551 (13 : ZMod 918423551)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (1669861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (1669861, 1)] : List FactorBlock).map factorBlockValue).prod) = 918423551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_1669861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 918423551) ^ 459211775 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 918423551) ^ 183684710 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 918423551) ^ 83493050 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 918423551) ^ 550 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_963983723 : Nat.Prime 963983723 := by
  apply lucas_primality 963983723 (2 : ZMod 963983723)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (1278493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (1278493, 1)] : List FactorBlock).map factorBlockValue).prod) = 963983723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_29
      · exact prime_oneHundredFortyTwoEJ_1278493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 963983723) ^ 481991861 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 963983723) ^ 74152594 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 963983723) ^ 33240818 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 963983723) ^ 754 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_974918333 : Nat.Prime 974918333 := by
  apply lucas_primality 974918333 (2 : ZMod 974918333)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (1399, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (1399, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) = 974918333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_83
      · exact prime_oneHundredFortyTwoEJ_1399
      · exact prime_oneHundredFortyTwoEJ_2099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 974918333) ^ 487459166 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 974918333) ^ 11746004 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 974918333) ^ 696868 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 974918333) ^ 464468 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_999758939 : Nat.Prime 999758939 := by
  apply lucas_primality 999758939 (2 : ZMod 999758939)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (499879469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (499879469, 1)] : List FactorBlock).map factorBlockValue).prod) = 999758939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_499879469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 999758939) ^ 499879469 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 999758939) ^ 2 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1098462487 : Nat.Prime 1098462487 := by
  apply lucas_primality 1098462487 (5 : ZMod 1098462487)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (151, 1), (110221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (151, 1), (110221, 1)] : List FactorBlock).map factorBlockValue).prod) = 1098462487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_151
      · exact prime_oneHundredFortyTwoEJ_110221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1098462487) ^ 549231243 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1098462487) ^ 366154162 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1098462487) ^ 99860226 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1098462487) ^ 7274586 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1098462487) ^ 9966 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1217285549 : Nat.Prime 1217285549 := by
  apply lucas_primality 1217285549 (2 : ZMod 1217285549)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (304321387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (304321387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1217285549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_304321387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1217285549) ^ 608642774 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1217285549) ^ 4 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1264134199 : Nat.Prime 1264134199 := by
  apply lucas_primality 1264134199 (3 : ZMod 1264134199)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1489, 1), (141497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1489, 1), (141497, 1)] : List FactorBlock).map factorBlockValue).prod) = 1264134199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_1489
      · exact prime_oneHundredFortyTwoEJ_141497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1264134199) ^ 632067099 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1264134199) ^ 421378066 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1264134199) ^ 848982 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1264134199) ^ 8934 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1334176517 : Nat.Prime 1334176517 := by
  apply lucas_primality 1334176517 (2 : ZMod 1334176517)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (163, 1), (269, 1), (7607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (163, 1), (269, 1), (7607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1334176517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_163
      · exact prime_oneHundredFortyTwoEJ_269
      · exact prime_oneHundredFortyTwoEJ_7607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1334176517) ^ 667088258 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1334176517) ^ 8185132 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1334176517) ^ 4959764 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1334176517) ^ 175388 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1401563363 : Nat.Prime 1401563363 := by
  apply lucas_primality 1401563363 (2 : ZMod 1401563363)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12203, 1), (57427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12203, 1), (57427, 1)] : List FactorBlock).map factorBlockValue).prod) = 1401563363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_12203
      · exact prime_oneHundredFortyTwoEJ_57427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1401563363) ^ 700781681 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1401563363) ^ 114854 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1401563363) ^ 24406 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1448131777 : Nat.Prime 1448131777 := by
  apply lucas_primality 1448131777 (5 : ZMod 1448131777)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (13, 1), (82883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (13, 1), (82883, 1)] : List FactorBlock).map factorBlockValue).prod) = 1448131777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_82883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1448131777) ^ 724065888 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1448131777) ^ 482710592 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1448131777) ^ 206875968 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1448131777) ^ 111394752 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1448131777) ^ 17472 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1498297571 : Nat.Prime 1498297571 := by
  apply lucas_primality 1498297571 (2 : ZMod 1498297571)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (751, 1), (2591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (751, 1), (2591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1498297571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_751
      · exact prime_oneHundredFortyTwoEJ_2591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1498297571) ^ 749148785 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1498297571) ^ 299659514 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1498297571) ^ 214042510 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1498297571) ^ 136208870 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1498297571) ^ 1995070 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1498297571) ^ 578270 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1571294999 : Nat.Prime 1571294999 := by
  apply lucas_primality 1571294999 (7 : ZMod 1571294999)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (8633489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (8633489, 1)] : List FactorBlock).map factorBlockValue).prod) = 1571294999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_8633489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1571294999) ^ 785647499 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1571294999) ^ 224470714 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1571294999) ^ 120868846 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1571294999) ^ 182 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1698932423 : Nat.Prime 1698932423 := by
  apply lucas_primality 1698932423 (5 : ZMod 1698932423)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (77224201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (77224201, 1)] : List FactorBlock).map factorBlockValue).prod) = 1698932423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_77224201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1698932423) ^ 849466211 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1698932423) ^ 154448402 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1698932423) ^ 22 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1833246083 : Nat.Prime 1833246083 := by
  apply lucas_primality 1833246083 (2 : ZMod 1833246083)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22859, 1), (40099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22859, 1), (40099, 1)] : List FactorBlock).map factorBlockValue).prod) = 1833246083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_22859
      · exact prime_oneHundredFortyTwoEJ_40099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1833246083) ^ 916623041 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1833246083) ^ 80198 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1833246083) ^ 45718 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2024574551 : Nat.Prime 2024574551 := by
  apply lucas_primality 2024574551 (17 : ZMod 2024574551)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (40491491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (40491491, 1)] : List FactorBlock).map factorBlockValue).prod) = 2024574551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_40491491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 2024574551) ^ 1012287275 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (17 : ZMod 2024574551) ^ 404914910 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (17 : ZMod 2024574551) ^ 50 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2110404017 : Nat.Prime 2110404017 := by
  apply lucas_primality 2110404017 (3 : ZMod 2110404017)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (18842893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (18842893, 1)] : List FactorBlock).map factorBlockValue).prod) = 2110404017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_18842893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2110404017) ^ 1055202008 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2110404017) ^ 301486288 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2110404017) ^ 112 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2206776149 : Nat.Prime 2206776149 := by
  apply lucas_primality 2206776149 (2 : ZMod 2206776149)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (443, 1), (26497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (443, 1), (26497, 1)] : List FactorBlock).map factorBlockValue).prod) = 2206776149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_47
      · exact prime_oneHundredFortyTwoEJ_443
      · exact prime_oneHundredFortyTwoEJ_26497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2206776149) ^ 1103388074 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2206776149) ^ 46952684 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2206776149) ^ 4981436 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2206776149) ^ 83284 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2282187727 : Nat.Prime 2282187727 := by
  apply lucas_primality 2282187727 (7 : ZMod 2282187727)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (151, 1), (9227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (151, 1), (9227, 1)] : List FactorBlock).map factorBlockValue).prod) = 2282187727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_151
      · exact prime_oneHundredFortyTwoEJ_9227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2282187727) ^ 1141093863 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2282187727) ^ 760729242 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2282187727) ^ 326026818 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2282187727) ^ 175552902 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2282187727) ^ 15113826 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2282187727) ^ 247338 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2378329463 : Nat.Prime 2378329463 := by
  apply lucas_primality 2378329463 (5 : ZMod 2378329463)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20353, 1), (58427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20353, 1), (58427, 1)] : List FactorBlock).map factorBlockValue).prod) = 2378329463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_20353
      · exact prime_oneHundredFortyTwoEJ_58427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2378329463) ^ 1189164731 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2378329463) ^ 116854 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2378329463) ^ 40706 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2585667229 : Nat.Prime 2585667229 := by
  apply lucas_primality 2585667229 (2 : ZMod 2585667229)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (1181, 1), (4243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (1181, 1), (4243, 1)] : List FactorBlock).map factorBlockValue).prod) = 2585667229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_43
      · exact prime_oneHundredFortyTwoEJ_1181
      · exact prime_oneHundredFortyTwoEJ_4243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2585667229) ^ 1292833614 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2585667229) ^ 861889076 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2585667229) ^ 60131796 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2585667229) ^ 2189388 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2585667229) ^ 609396 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2803126727 : Nat.Prime 2803126727 := by
  apply lucas_primality 2803126727 (5 : ZMod 2803126727)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1401563363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1401563363, 1)] : List FactorBlock).map factorBlockValue).prod) = 2803126727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_1401563363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 2803126727) ^ 1401563363 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2803126727) ^ 2 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3708193927 : Nat.Prime 3708193927 := by
  apply lucas_primality 3708193927 (3 : ZMod 3708193927)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (107, 1), (86209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (107, 1), (86209, 1)] : List FactorBlock).map factorBlockValue).prod) = 3708193927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_67
      · exact prime_oneHundredFortyTwoEJ_107
      · exact prime_oneHundredFortyTwoEJ_86209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3708193927) ^ 1854096963 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3708193927) ^ 1236064642 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3708193927) ^ 55346178 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3708193927) ^ 34656018 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3708193927) ^ 43014 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_4220329013 : Nat.Prime 4220329013 := by
  apply lucas_primality 4220329013 (2 : ZMod 4220329013)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (2003, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (2003, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) = 4220329013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_131
      · exact prime_oneHundredFortyTwoEJ_2003
      · exact prime_oneHundredFortyTwoEJ_4021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4220329013) ^ 2110164506 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4220329013) ^ 32216252 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4220329013) ^ 2107004 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4220329013) ^ 1049572 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_5330282851 : Nat.Prime 5330282851 := by
  apply lucas_primality 5330282851 (11 : ZMod 5330282851)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (17, 1), (587, 1), (1187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (17, 1), (587, 1), (1187, 1)] : List FactorBlock).map factorBlockValue).prod) = 5330282851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_587
      · exact prime_oneHundredFortyTwoEJ_1187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5330282851) ^ 2665141425 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5330282851) ^ 1776760950 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5330282851) ^ 1066056570 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5330282851) ^ 313546050 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5330282851) ^ 9080550 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 5330282851) ^ 4490550 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_6015017257 : Nat.Prime 6015017257 := by
  apply lucas_primality 6015017257 (5 : ZMod 6015017257)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8231, 1), (30449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8231, 1), (30449, 1)] : List FactorBlock).map factorBlockValue).prod) = 6015017257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_8231
      · exact prime_oneHundredFortyTwoEJ_30449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6015017257) ^ 3007508628 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6015017257) ^ 2005005752 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6015017257) ^ 730776 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6015017257) ^ 197544 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_7248391259 : Nat.Prime 7248391259 := by
  apply lucas_primality 7248391259 (2 : ZMod 7248391259)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (157573723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (157573723, 1)] : List FactorBlock).map factorBlockValue).prod) = 7248391259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_157573723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7248391259) ^ 3624195629 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7248391259) ^ 315147446 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7248391259) ^ 46 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_7821480379 : Nat.Prime 7821480379 := by
  apply lucas_primality 7821480379 (2 : ZMod 7821480379)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (89, 1), (761, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (89, 1), (761, 1), (1013, 1)] : List FactorBlock).map factorBlockValue).prod) = 7821480379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_89
      · exact prime_oneHundredFortyTwoEJ_761
      · exact prime_oneHundredFortyTwoEJ_1013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7821480379) ^ 3910740189 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7821480379) ^ 2607160126 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7821480379) ^ 411656862 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7821480379) ^ 87881802 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7821480379) ^ 10277898 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7821480379) ^ 7721106 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_8174106049 : Nat.Prime 8174106049 := by
  apply lucas_primality 8174106049 (11 : ZMod 8174106049)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (53, 1), (803273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (53, 1), (803273, 1)] : List FactorBlock).map factorBlockValue).prod) = 8174106049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_53
      · exact prime_oneHundredFortyTwoEJ_803273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 8174106049) ^ 4087053024 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 8174106049) ^ 2724702016 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 8174106049) ^ 154228416 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 8174106049) ^ 10176 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_8207857571 : Nat.Prime 8207857571 := by
  apply lucas_primality 8207857571 (2 : ZMod 8207857571)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (59, 1), (641, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (59, 1), (641, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) = 8207857571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_59
      · exact prime_oneHundredFortyTwoEJ_641
      · exact prime_oneHundredFortyTwoEJ_1973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8207857571) ^ 4103928785 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8207857571) ^ 1641571514 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8207857571) ^ 746168870 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8207857571) ^ 139116230 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8207857571) ^ 12804770 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8207857571) ^ 4160090 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_8317066267 : Nat.Prime 8317066267 := by
  apply lucas_primality 8317066267 (2 : ZMod 8317066267)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (16451, 1), (28087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (16451, 1), (28087, 1)] : List FactorBlock).map factorBlockValue).prod) = 8317066267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_16451
      · exact prime_oneHundredFortyTwoEJ_28087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8317066267) ^ 4158533133 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8317066267) ^ 2772355422 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8317066267) ^ 505566 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8317066267) ^ 296118 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_8694574633 : Nat.Prime 8694574633 := by
  apply lucas_primality 8694574633 (5 : ZMod 8694574633)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (23, 1), (487, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (23, 1), (487, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod) = 8694574633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_487
      · exact prime_oneHundredFortyTwoEJ_10781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8694574633) ^ 4347287316 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8694574633) ^ 2898191544 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8694574633) ^ 378024984 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8694574633) ^ 17853336 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8694574633) ^ 806472 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_8880469229 : Nat.Prime 8880469229 := by
  apply lucas_primality 8880469229 (2 : ZMod 8880469229)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (197, 1), (11269631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (197, 1), (11269631, 1)] : List FactorBlock).map factorBlockValue).prod) = 8880469229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_197
      · exact prime_oneHundredFortyTwoEJ_11269631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8880469229) ^ 4440234614 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8880469229) ^ 45078524 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8880469229) ^ 788 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_11961811601 : Nat.Prime 11961811601 := by
  apply lucas_primality 11961811601 (3 : ZMod 11961811601)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (373, 1), (80173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (373, 1), (80173, 1)] : List FactorBlock).map factorBlockValue).prod) = 11961811601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_373
      · exact prime_oneHundredFortyTwoEJ_80173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11961811601) ^ 5980905800 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11961811601) ^ 2392362320 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11961811601) ^ 32069200 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11961811601) ^ 149200 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_13268553583 : Nat.Prime 13268553583 := by
  apply lucas_primality 13268553583 (6 : ZMod 13268553583)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (269, 1), (357431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (269, 1), (357431, 1)] : List FactorBlock).map factorBlockValue).prod) = 13268553583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_269
      · exact prime_oneHundredFortyTwoEJ_357431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 13268553583) ^ 6634276791 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 13268553583) ^ 4422851194 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 13268553583) ^ 576893634 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 13268553583) ^ 49325478 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 13268553583) ^ 37122 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_14481317771 : Nat.Prime 14481317771 := by
  apply lucas_primality 14481317771 (6 : ZMod 14481317771)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1448131777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1448131777, 1)] : List FactorBlock).map factorBlockValue).prod) = 14481317771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_1448131777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 14481317771) ^ 7240658885 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14481317771) ^ 2896263554 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14481317771) ^ 10 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_14778170681 : Nat.Prime 14778170681 := by
  apply lucas_primality 14778170681 (6 : ZMod 14778170681)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 2), (13, 1), (23, 1), (151, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 2), (13, 1), (23, 1), (151, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) = 14778170681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_151
      · exact prime_oneHundredFortyTwoEJ_167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14778170681) ^ 7389085340 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14778170681) ^ 2955634136 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14778170681) ^ 2111167240 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14778170681) ^ 1136782360 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14778170681) ^ 642529160 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14778170681) ^ 97868680 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14778170681) ^ 88492040 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_15674212231 : Nat.Prime 15674212231 := by
  apply lucas_primality 15674212231 (12 : ZMod 15674212231)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (151, 1), (3460091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (151, 1), (3460091, 1)] : List FactorBlock).map factorBlockValue).prod) = 15674212231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_151
      · exact prime_oneHundredFortyTwoEJ_3460091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 15674212231) ^ 7837106115 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (12 : ZMod 15674212231) ^ 5224737410 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (12 : ZMod 15674212231) ^ 3134842446 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (12 : ZMod 15674212231) ^ 103802730 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (12 : ZMod 15674212231) ^ 4530 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_16617987697 : Nat.Prime 16617987697 := by
  apply lucas_primality 16617987697 (5 : ZMod 16617987697)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (431, 1), (47251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (431, 1), (47251, 1)] : List FactorBlock).map factorBlockValue).prod) = 16617987697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_431
      · exact prime_oneHundredFortyTwoEJ_47251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16617987697) ^ 8308993848 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 16617987697) ^ 5539329232 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 16617987697) ^ 977528688 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 16617987697) ^ 38556816 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 16617987697) ^ 351696 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_17925588013 : Nat.Prime 17925588013 := by
  apply lucas_primality 17925588013 (5 : ZMod 17925588013)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (24733, 1), (60397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (24733, 1), (60397, 1)] : List FactorBlock).map factorBlockValue).prod) = 17925588013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_24733
      · exact prime_oneHundredFortyTwoEJ_60397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17925588013) ^ 8962794006 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17925588013) ^ 5975196004 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17925588013) ^ 724764 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 17925588013) ^ 296796 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_18012383041 : Nat.Prime 18012383041 := by
  apply lucas_primality 18012383041 (29 : ZMod 18012383041)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (19, 1), (499, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (19, 1), (499, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod) = 18012383041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_499
      · exact prime_oneHundredFortyTwoEJ_1979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 18012383041) ^ 9006191520 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (29 : ZMod 18012383041) ^ 6004127680 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (29 : ZMod 18012383041) ^ 3602476608 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (29 : ZMod 18012383041) ^ 948020160 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (29 : ZMod 18012383041) ^ 36096960 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (29 : ZMod 18012383041) ^ 9101760 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_19667043553 : Nat.Prime 19667043553 := by
  apply lucas_primality 19667043553 (5 : ZMod 19667043553)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (653, 1), (24133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (653, 1), (24133, 1)] : List FactorBlock).map factorBlockValue).prod) = 19667043553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_653
      · exact prime_oneHundredFortyTwoEJ_24133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19667043553) ^ 9833521776 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 19667043553) ^ 6555681184 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 19667043553) ^ 1512849504 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 19667043553) ^ 30117984 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 19667043553) ^ 814944 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_21654801673 : Nat.Prime 21654801673 := by
  apply lucas_primality 21654801673 (10 : ZMod 21654801673)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (163, 1), (173, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (163, 1), (173, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) = 21654801673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_163
      · exact prime_oneHundredFortyTwoEJ_173
      · exact prime_oneHundredFortyTwoEJ_653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 21654801673) ^ 10827400836 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 21654801673) ^ 7218267224 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 21654801673) ^ 3093543096 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 21654801673) ^ 132851544 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 21654801673) ^ 125172264 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 21654801673) ^ 33162024 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_27588487211 : Nat.Prime 27588487211 := by
  apply lucas_primality 27588487211 (2 : ZMod 27588487211)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12253, 1), (225157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12253, 1), (225157, 1)] : List FactorBlock).map factorBlockValue).prod) = 27588487211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_12253
      · exact prime_oneHundredFortyTwoEJ_225157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27588487211) ^ 13794243605 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27588487211) ^ 5517697442 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27588487211) ^ 2251570 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27588487211) ^ 122530 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_30847479137 : Nat.Prime 30847479137 := by
  apply lucas_primality 30847479137 (3 : ZMod 30847479137)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (963983723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (963983723, 1)] : List FactorBlock).map factorBlockValue).prod) = 30847479137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_963983723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 30847479137) ^ 15423739568 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 30847479137) ^ 32 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_32569120651 : Nat.Prime 32569120651 := by
  apply lucas_primality 32569120651 (7 : ZMod 32569120651)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (79, 1), (249859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (79, 1), (249859, 1)] : List FactorBlock).map factorBlockValue).prod) = 32569120651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_79
      · exact prime_oneHundredFortyTwoEJ_249859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32569120651) ^ 16284560325 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 32569120651) ^ 10856373550 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 32569120651) ^ 6513824130 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 32569120651) ^ 2960829150 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 32569120651) ^ 412267350 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 32569120651) ^ 130350 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_32881450757 : Nat.Prime 32881450757 := by
  apply lucas_primality 32881450757 (2 : ZMod 32881450757)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (2011, 1), (53087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (2011, 1), (53087, 1)] : List FactorBlock).map factorBlockValue).prod) = 32881450757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_2011
      · exact prime_oneHundredFortyTwoEJ_53087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32881450757) ^ 16440725378 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32881450757) ^ 4697350108 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32881450757) ^ 2989222796 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32881450757) ^ 16350796 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32881450757) ^ 619388 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_33185311979 : Nat.Prime 33185311979 := by
  apply lucas_primality 33185311979 (2 : ZMod 33185311979)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (151, 1), (1207529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (151, 1), (1207529, 1)] : List FactorBlock).map factorBlockValue).prod) = 33185311979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_151
      · exact prime_oneHundredFortyTwoEJ_1207529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33185311979) ^ 16592655989 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 33185311979) ^ 4740758854 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 33185311979) ^ 2552716306 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 33185311979) ^ 219770278 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 33185311979) ^ 27482 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_35239493909 : Nat.Prime 35239493909 := by
  apply lucas_primality 35239493909 (2 : ZMod 35239493909)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (503, 1), (564989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (503, 1), (564989, 1)] : List FactorBlock).map factorBlockValue).prod) = 35239493909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_503
      · exact prime_oneHundredFortyTwoEJ_564989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35239493909) ^ 17619746954 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 35239493909) ^ 1136757868 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 35239493909) ^ 70058636 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 35239493909) ^ 62372 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_36693185933 : Nat.Prime 36693185933 := by
  apply lucas_primality 36693185933 (2 : ZMod 36693185933)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (79, 1), (89, 1), (100361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (79, 1), (89, 1), (100361, 1)] : List FactorBlock).map factorBlockValue).prod) = 36693185933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_79
      · exact prime_oneHundredFortyTwoEJ_89
      · exact prime_oneHundredFortyTwoEJ_100361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36693185933) ^ 18346592966 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 36693185933) ^ 2822552764 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 36693185933) ^ 464470708 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 36693185933) ^ 412282988 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 36693185933) ^ 365612 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_39685628261 : Nat.Prime 39685628261 := by
  apply lucas_primality 39685628261 (7 : ZMod 39685628261)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (1151, 1), (59447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (1151, 1), (59447, 1)] : List FactorBlock).map factorBlockValue).prod) = 39685628261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_29
      · exact prime_oneHundredFortyTwoEJ_1151
      · exact prime_oneHundredFortyTwoEJ_59447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 39685628261) ^ 19842814130 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 39685628261) ^ 7937125652 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 39685628261) ^ 1368469940 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 39685628261) ^ 34479260 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 39685628261) ^ 667580 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_51735056017 : Nat.Prime 51735056017 := by
  apply lucas_primality 51735056017 (5 : ZMod 51735056017)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (1061, 1), (145121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (1061, 1), (145121, 1)] : List FactorBlock).map factorBlockValue).prod) = 51735056017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_1061
      · exact prime_oneHundredFortyTwoEJ_145121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 51735056017) ^ 25867528008 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 51735056017) ^ 17245018672 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 51735056017) ^ 7390722288 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 51735056017) ^ 48760656 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 51735056017) ^ 356496 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_52690233769 : Nat.Prime 52690233769 := by
  apply lucas_primality 52690233769 (14 : ZMod 52690233769)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (643, 1), (3414349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (643, 1), (3414349, 1)] : List FactorBlock).map factorBlockValue).prod) = 52690233769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_643
      · exact prime_oneHundredFortyTwoEJ_3414349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 52690233769) ^ 26345116884 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 52690233769) ^ 17563411256 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 52690233769) ^ 81944376 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 52690233769) ^ 15432 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_66481855457 : Nat.Prime 66481855457 := by
  apply lucas_primality 66481855457 (3 : ZMod 66481855457)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (109345157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (109345157, 1)] : List FactorBlock).map factorBlockValue).prod) = 66481855457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_109345157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 66481855457) ^ 33240927728 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 66481855457) ^ 3499045024 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 66481855457) ^ 608 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_68234911229 : Nat.Prime 68234911229 := by
  apply lucas_primality 68234911229 (2 : ZMod 68234911229)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (29209, 1), (53093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (29209, 1), (53093, 1)] : List FactorBlock).map factorBlockValue).prod) = 68234911229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_29209
      · exact prime_oneHundredFortyTwoEJ_53093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68234911229) ^ 34117455614 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68234911229) ^ 6203173748 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68234911229) ^ 2336092 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68234911229) ^ 1285196 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_73719530683 : Nat.Prime 73719530683 := by
  apply lucas_primality 73719530683 (2 : ZMod 73719530683)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (211, 1), (439, 1), (2707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (211, 1), (439, 1), (2707, 1)] : List FactorBlock).map factorBlockValue).prod) = 73719530683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_211
      · exact prime_oneHundredFortyTwoEJ_439
      · exact prime_oneHundredFortyTwoEJ_2707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73719530683) ^ 36859765341 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 73719530683) ^ 24573176894 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 73719530683) ^ 10531361526 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 73719530683) ^ 349381662 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 73719530683) ^ 167926038 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 73719530683) ^ 27232926 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_85276156639 : Nat.Prime 85276156639 := by
  apply lucas_primality 85276156639 (6 : ZMod 85276156639)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6959, 1), (2042347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6959, 1), (2042347, 1)] : List FactorBlock).map factorBlockValue).prod) = 85276156639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_6959
      · exact prime_oneHundredFortyTwoEJ_2042347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 85276156639) ^ 42638078319 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 85276156639) ^ 28425385546 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 85276156639) ^ 12254082 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 85276156639) ^ 41754 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_107871726337 : Nat.Prime 107871726337 := by
  apply lucas_primality 107871726337 (10 : ZMod 107871726337)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (11, 1), (12768907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (11, 1), (12768907, 1)] : List FactorBlock).map factorBlockValue).prod) = 107871726337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_12768907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 107871726337) ^ 53935863168 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 107871726337) ^ 35957242112 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 107871726337) ^ 9806520576 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 107871726337) ^ 8448 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_116243073181 : Nat.Prime 116243073181 := by
  apply lucas_primality 116243073181 (10 : ZMod 116243073181)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (23, 1), (157, 1), (13757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (23, 1), (157, 1), (13757, 1)] : List FactorBlock).map factorBlockValue).prod) = 116243073181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_157
      · exact prime_oneHundredFortyTwoEJ_13757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 116243073181) ^ 58121536590 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 116243073181) ^ 38747691060 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 116243073181) ^ 23248614636 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 116243073181) ^ 8941774860 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 116243073181) ^ 5054046660 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 116243073181) ^ 740401740 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 116243073181) ^ 8449740 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_130401774823 : Nat.Prime 130401774823 := by
  apply lucas_primality 130401774823 (5 : ZMod 130401774823)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (109, 1), (2423, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (109, 1), (2423, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) = 130401774823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_109
      · exact prime_oneHundredFortyTwoEJ_2423
      · exact prime_oneHundredFortyTwoEJ_7481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 130401774823) ^ 65200887411 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 130401774823) ^ 43467258274 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 130401774823) ^ 11854706802 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 130401774823) ^ 1196346558 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 130401774823) ^ 53818314 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 130401774823) ^ 17431062 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_185369196517 : Nat.Prime 185369196517 := by
  apply lucas_primality 185369196517 (2 : ZMod 185369196517)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (2206776149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (2206776149, 1)] : List FactorBlock).map factorBlockValue).prod) = 185369196517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_2206776149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 185369196517) ^ 92684598258 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 185369196517) ^ 61789732172 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 185369196517) ^ 26481313788 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 185369196517) ^ 84 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_261443815891 : Nat.Prime 261443815891 := by
  apply lucas_primality 261443815891 (3 : ZMod 261443815891)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (173, 1), (191, 1), (11467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (173, 1), (191, 1), (11467, 1)] : List FactorBlock).map factorBlockValue).prod) = 261443815891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_173
      · exact prime_oneHundredFortyTwoEJ_191
      · exact prime_oneHundredFortyTwoEJ_11467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 261443815891) ^ 130721907945 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 261443815891) ^ 87147938630 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 261443815891) ^ 52288763178 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 261443815891) ^ 11367122430 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 261443815891) ^ 1511235930 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 261443815891) ^ 1368815790 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 261443815891) ^ 22799670 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_277466003027 : Nat.Prime 277466003027 := by
  apply lucas_primality 277466003027 (2 : ZMod 277466003027)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (97, 1), (1951, 1), (31873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (97, 1), (1951, 1), (31873, 1)] : List FactorBlock).map factorBlockValue).prod) = 277466003027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_97
      · exact prime_oneHundredFortyTwoEJ_1951
      · exact prime_oneHundredFortyTwoEJ_31873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 277466003027) ^ 138733001513 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 277466003027) ^ 12063739262 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 277466003027) ^ 2860474258 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 277466003027) ^ 142217326 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 277466003027) ^ 8705362 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_284702664187 : Nat.Prime 284702664187 := by
  apply lucas_primality 284702664187 (2 : ZMod 284702664187)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (211, 1), (925447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (211, 1), (925447, 1)] : List FactorBlock).map factorBlockValue).prod) = 284702664187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_211
      · exact prime_oneHundredFortyTwoEJ_925447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 284702664187) ^ 142351332093 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 284702664187) ^ 94900888062 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 284702664187) ^ 1349301726 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 284702664187) ^ 307638 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_287046201889 : Nat.Prime 287046201889 := by
  apply lucas_primality 287046201889 (7 : ZMod 287046201889)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (107, 1), (677, 1), (13759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (107, 1), (677, 1), (13759, 1)] : List FactorBlock).map factorBlockValue).prod) = 287046201889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_107
      · exact prime_oneHundredFortyTwoEJ_677
      · exact prime_oneHundredFortyTwoEJ_13759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 287046201889) ^ 143523100944 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 287046201889) ^ 95682067296 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 287046201889) ^ 2682674784 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 287046201889) ^ 423997344 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 287046201889) ^ 20862432 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_296958804113 : Nat.Prime 296958804113 := by
  apply lucas_primality 296958804113 (3 : ZMod 296958804113)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (53, 1), (350187269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (53, 1), (350187269, 1)] : List FactorBlock).map factorBlockValue).prod) = 296958804113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_53
      · exact prime_oneHundredFortyTwoEJ_350187269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 296958804113) ^ 148479402056 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 296958804113) ^ 5602996304 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 296958804113) ^ 848 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_339127710419 : Nat.Prime 339127710419 := by
  apply lucas_primality 339127710419 (2 : ZMod 339127710419)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (494355263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (494355263, 1)] : List FactorBlock).map factorBlockValue).prod) = 339127710419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_494355263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 339127710419) ^ 169563855209 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 339127710419) ^ 48446815774 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 339127710419) ^ 686 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_380814619387 : Nat.Prime 380814619387 := by
  apply lucas_primality 380814619387 (2 : ZMod 380814619387)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (32321, 1), (1963711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (32321, 1), (1963711, 1)] : List FactorBlock).map factorBlockValue).prod) = 380814619387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_32321
      · exact prime_oneHundredFortyTwoEJ_1963711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 380814619387) ^ 190407309693 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 380814619387) ^ 126938206462 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 380814619387) ^ 11782266 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 380814619387) ^ 193926 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_428136865297 : Nat.Prime 428136865297 := by
  apply lucas_primality 428136865297 (5 : ZMod 428136865297)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (17, 1), (61, 1), (137, 1), (8969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (17, 1), (61, 1), (137, 1), (8969, 1)] : List FactorBlock).map factorBlockValue).prod) = 428136865297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_61
      · exact prime_oneHundredFortyTwoEJ_137
      · exact prime_oneHundredFortyTwoEJ_8969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 428136865297) ^ 214068432648 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 428136865297) ^ 142712288432 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 428136865297) ^ 61162409328 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 428136865297) ^ 25184521488 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 428136865297) ^ 7018637136 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 428136865297) ^ 3125086608 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 428136865297) ^ 47735184 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_497208349831 : Nat.Prime 497208349831 := by
  apply lucas_primality 497208349831 (6 : ZMod 497208349831)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (974918333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (974918333, 1)] : List FactorBlock).map factorBlockValue).prod) = 497208349831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_974918333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 497208349831) ^ 248604174915 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 497208349831) ^ 165736116610 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 497208349831) ^ 99441669966 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 497208349831) ^ 29247549990 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 497208349831) ^ 510 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_514183097167 : Nat.Prime 514183097167 := by
  apply lucas_primality 514183097167 (6 : ZMod 514183097167)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (281, 1), (304972181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (281, 1), (304972181, 1)] : List FactorBlock).map factorBlockValue).prod) = 514183097167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_281
      · exact prime_oneHundredFortyTwoEJ_304972181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 514183097167) ^ 257091548583 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 514183097167) ^ 171394365722 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 514183097167) ^ 1829833086 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 514183097167) ^ 1686 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_644835414221 : Nat.Prime 644835414221 := by
  apply lucas_primality 644835414221 (2 : ZMod 644835414221)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1427, 1), (22594093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1427, 1), (22594093, 1)] : List FactorBlock).map factorBlockValue).prod) = 644835414221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_1427
      · exact prime_oneHundredFortyTwoEJ_22594093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 644835414221) ^ 322417707110 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 644835414221) ^ 128967082844 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 644835414221) ^ 451881860 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 644835414221) ^ 28540 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_678255420839 : Nat.Prime 678255420839 := by
  apply lucas_primality 678255420839 (17 : ZMod 678255420839)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (339127710419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (339127710419, 1)] : List FactorBlock).map factorBlockValue).prod) = 678255420839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_339127710419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 678255420839) ^ 339127710419 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (17 : ZMod 678255420839) ^ 2 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_718453857241 : Nat.Prime 718453857241 := by
  apply lucas_primality 718453857241 (19 : ZMod 718453857241)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 1), (95033579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 1), (95033579, 1)] : List FactorBlock).map factorBlockValue).prod) = 718453857241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_95033579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 718453857241) ^ 359226928620 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 718453857241) ^ 239484619080 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 718453857241) ^ 143690771448 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 718453857241) ^ 102636265320 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 718453857241) ^ 7560 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_781846452469 : Nat.Prime 781846452469 := by
  apply lucas_primality 781846452469 (2 : ZMod 781846452469)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (144583, 1), (150211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (144583, 1), (150211, 1)] : List FactorBlock).map factorBlockValue).prod) = 781846452469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_144583
      · exact prime_oneHundredFortyTwoEJ_150211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 781846452469) ^ 390923226234 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 781846452469) ^ 260615484156 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 781846452469) ^ 5407596 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 781846452469) ^ 5204988 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_786555838181 : Nat.Prime 786555838181 := by
  apply lucas_primality 786555838181 (2 : ZMod 786555838181)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (773, 1), (7268119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (773, 1), (7268119, 1)] : List FactorBlock).map factorBlockValue).prod) = 786555838181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_773
      · exact prime_oneHundredFortyTwoEJ_7268119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 786555838181) ^ 393277919090 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 786555838181) ^ 157311167636 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 786555838181) ^ 112365119740 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 786555838181) ^ 1017536660 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 786555838181) ^ 108220 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_821785742707 : Nat.Prime 821785742707 := by
  apply lucas_primality 821785742707 (13 : ZMod 821785742707)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (14629, 1), (217733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (14629, 1), (217733, 1)] : List FactorBlock).map factorBlockValue).prod) = 821785742707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_43
      · exact prime_oneHundredFortyTwoEJ_14629
      · exact prime_oneHundredFortyTwoEJ_217733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 821785742707) ^ 410892871353 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 821785742707) ^ 273928580902 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 821785742707) ^ 19111296342 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 821785742707) ^ 56175114 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 821785742707) ^ 3774282 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_882049563569 : Nat.Prime 882049563569 := by
  apply lucas_primality 882049563569 (3 : ZMod 882049563569)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (31, 1), (1471, 1), (41687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (31, 1), (1471, 1), (41687, 1)] : List FactorBlock).map factorBlockValue).prod) = 882049563569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_29
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_1471
      · exact prime_oneHundredFortyTwoEJ_41687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 882049563569) ^ 441024781784 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 882049563569) ^ 30415502192 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 882049563569) ^ 28453211728 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 882049563569) ^ 599625808 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 882049563569) ^ 21158864 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_937987575659 : Nat.Prime 937987575659 := by
  apply lucas_primality 937987575659 (2 : ZMod 937987575659)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (53, 1), (1264134199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (53, 1), (1264134199, 1)] : List FactorBlock).map factorBlockValue).prod) = 937987575659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_53
      · exact prime_oneHundredFortyTwoEJ_1264134199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 937987575659) ^ 468993787829 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 937987575659) ^ 133998225094 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 937987575659) ^ 17697878786 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 937987575659) ^ 742 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_947767334281 : Nat.Prime 947767334281 := by
  apply lucas_primality 947767334281 (7 : ZMod 947767334281)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (607543163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (607543163, 1)] : List FactorBlock).map factorBlockValue).prod) = 947767334281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_607543163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 947767334281) ^ 473883667140 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 947767334281) ^ 315922444760 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 947767334281) ^ 189553466856 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 947767334281) ^ 72905179560 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 947767334281) ^ 1560 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_957565178891 : Nat.Prime 957565178891 := by
  apply lucas_primality 957565178891 (6 : ZMod 957565178891)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (37, 1), (136211263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (37, 1), (136211263, 1)] : List FactorBlock).map factorBlockValue).prod) = 957565178891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_37
      · exact prime_oneHundredFortyTwoEJ_136211263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 957565178891) ^ 478782589445 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 957565178891) ^ 191513035778 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 957565178891) ^ 50398167310 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 957565178891) ^ 25880139970 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 957565178891) ^ 7030 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_995647773511 : Nat.Prime 995647773511 := by
  apply lucas_primality 995647773511 (30 : ZMod 995647773511)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (67, 1), (12701209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (67, 1), (12701209, 1)] : List FactorBlock).map factorBlockValue).prod) = 995647773511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_67
      · exact prime_oneHundredFortyTwoEJ_12701209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (30 : ZMod 995647773511) ^ 497823886755 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (30 : ZMod 995647773511) ^ 331882591170 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (30 : ZMod 995647773511) ^ 199129554702 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (30 : ZMod 995647773511) ^ 76588290270 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (30 : ZMod 995647773511) ^ 14860414530 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (30 : ZMod 995647773511) ^ 78390 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1114511899603 : Nat.Prime 1114511899603 := by
  apply lucas_primality 1114511899603 (2 : ZMod 1114511899603)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (72559, 1), (150589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (72559, 1), (150589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1114511899603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_72559
      · exact prime_oneHundredFortyTwoEJ_150589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1114511899603) ^ 557255949801 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1114511899603) ^ 371503966534 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1114511899603) ^ 65559523506 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1114511899603) ^ 15360078 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1114511899603) ^ 7401018 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1281461814467 : Nat.Prime 1281461814467 := by
  apply lucas_primality 1281461814467 (2 : ZMod 1281461814467)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (263, 1), (78588361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (263, 1), (78588361, 1)] : List FactorBlock).map factorBlockValue).prod) = 1281461814467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_263
      · exact prime_oneHundredFortyTwoEJ_78588361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1281461814467) ^ 640730907233 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1281461814467) ^ 41337477886 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1281461814467) ^ 4872478382 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1281461814467) ^ 16306 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1393131567923 : Nat.Prime 1393131567923 := by
  apply lucas_primality 1393131567923 (2 : ZMod 1393131567923)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (65963, 1), (10559947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (65963, 1), (10559947, 1)] : List FactorBlock).map factorBlockValue).prod) = 1393131567923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_65963
      · exact prime_oneHundredFortyTwoEJ_10559947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1393131567923) ^ 696565783961 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1393131567923) ^ 21119894 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1393131567923) ^ 131926 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1452762566279 : Nat.Prime 1452762566279 := by
  apply lucas_primality 1452762566279 (13 : ZMod 1452762566279)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (419, 1), (19478729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (419, 1), (19478729, 1)] : List FactorBlock).map factorBlockValue).prod) = 1452762566279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_89
      · exact prime_oneHundredFortyTwoEJ_419
      · exact prime_oneHundredFortyTwoEJ_19478729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1452762566279) ^ 726381283139 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 1452762566279) ^ 16323174902 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 1452762566279) ^ 3467213762 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 1452762566279) ^ 74582 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1508117842927 : Nat.Prime 1508117842927 := by
  apply lucas_primality 1508117842927 (3 : ZMod 1508117842927)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (227, 1), (2817511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (227, 1), (2817511, 1)] : List FactorBlock).map factorBlockValue).prod) = 1508117842927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_131
      · exact prime_oneHundredFortyTwoEJ_227
      · exact prime_oneHundredFortyTwoEJ_2817511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1508117842927) ^ 754058921463 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508117842927) ^ 502705947642 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508117842927) ^ 11512349946 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508117842927) ^ 6643690938 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508117842927) ^ 535266 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1612188424909 : Nat.Prime 1612188424909 := by
  apply lucas_primality 1612188424909 (6 : ZMod 1612188424909)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (45833, 1), (325697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (45833, 1), (325697, 1)] : List FactorBlock).map factorBlockValue).prod) = 1612188424909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_45833
      · exact prime_oneHundredFortyTwoEJ_325697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1612188424909) ^ 806094212454 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1612188424909) ^ 537396141636 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1612188424909) ^ 35175276 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 1612188424909) ^ 4949964 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2154005008123 : Nat.Prime 2154005008123 := by
  apply lucas_primality 2154005008123 (2 : ZMod 2154005008123)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (19, 1), (1283, 1), (121711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (19, 1), (1283, 1), (121711, 1)] : List FactorBlock).map factorBlockValue).prod) = 2154005008123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_1283
      · exact prime_oneHundredFortyTwoEJ_121711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2154005008123) ^ 1077002504061 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2154005008123) ^ 718001669374 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2154005008123) ^ 195818637102 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2154005008123) ^ 113368684638 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2154005008123) ^ 1678881534 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2154005008123) ^ 17697702 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2610823801657 : Nat.Prime 2610823801657 := by
  apply lucas_primality 2610823801657 (5 : ZMod 2610823801657)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (2671, 1), (5818277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (2671, 1), (5818277, 1)] : List FactorBlock).map factorBlockValue).prod) = 2610823801657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_2671
      · exact prime_oneHundredFortyTwoEJ_5818277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2610823801657) ^ 1305411900828 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2610823801657) ^ 870274600552 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2610823801657) ^ 372974828808 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2610823801657) ^ 977470536 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2610823801657) ^ 448728 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2940223561559 : Nat.Prime 2940223561559 := by
  apply lucas_primality 2940223561559 (7 : ZMod 2940223561559)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (830989, 1), (1769111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (830989, 1), (1769111, 1)] : List FactorBlock).map factorBlockValue).prod) = 2940223561559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_830989
      · exact prime_oneHundredFortyTwoEJ_1769111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2940223561559) ^ 1470111780779 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2940223561559) ^ 3538222 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2940223561559) ^ 1661978 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2948781227321 : Nat.Prime 2948781227321 := by
  apply lucas_primality 2948781227321 (3 : ZMod 2948781227321)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (73719530683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (73719530683, 1)] : List FactorBlock).map factorBlockValue).prod) = 2948781227321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_73719530683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2948781227321) ^ 1474390613660 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2948781227321) ^ 589756245464 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2948781227321) ^ 40 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2993953682371 : Nat.Prime 2993953682371 := by
  apply lucas_primality 2993953682371 (7 : ZMod 2993953682371)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (20399, 1), (698903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (20399, 1), (698903, 1)] : List FactorBlock).map factorBlockValue).prod) = 2993953682371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_20399
      · exact prime_oneHundredFortyTwoEJ_698903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2993953682371) ^ 1496976841185 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2993953682371) ^ 997984560790 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2993953682371) ^ 598790736474 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2993953682371) ^ 427707668910 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2993953682371) ^ 146769630 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2993953682371) ^ 4283790 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3945228598639 : Nat.Prime 3945228598639 := by
  apply lucas_primality 3945228598639 (6 : ZMod 3945228598639)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (1201, 1), (3443347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (1201, 1), (3443347, 1)] : List FactorBlock).map factorBlockValue).prod) = 3945228598639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_53
      · exact prime_oneHundredFortyTwoEJ_1201
      · exact prime_oneHundredFortyTwoEJ_3443347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3945228598639) ^ 1972614299319 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3945228598639) ^ 1315076199546 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3945228598639) ^ 74438275446 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3945228598639) ^ 3284953038 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3945228598639) ^ 1145754 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_4601638490971 : Nat.Prime 4601638490971 := by
  apply lucas_primality 4601638490971 (2 : ZMod 4601638490971)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1259, 1), (3527, 1), (34543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1259, 1), (3527, 1), (34543, 1)] : List FactorBlock).map factorBlockValue).prod) = 4601638490971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_1259
      · exact prime_oneHundredFortyTwoEJ_3527
      · exact prime_oneHundredFortyTwoEJ_34543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4601638490971) ^ 2300819245485 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4601638490971) ^ 1533879496990 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4601638490971) ^ 920327698194 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4601638490971) ^ 3654994830 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4601638490971) ^ 1304689110 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4601638490971) ^ 133214790 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_5290724305189 : Nat.Prime 5290724305189 := by
  apply lucas_primality 5290724305189 (10 : ZMod 5290724305189)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 2), (999758939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 2), (999758939, 1)] : List FactorBlock).map factorBlockValue).prod) = 5290724305189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_999758939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 5290724305189) ^ 2645362152594 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 5290724305189) ^ 1763574768396 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 5290724305189) ^ 755817757884 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 5290724305189) ^ 5292 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_5897562454643 : Nat.Prime 5897562454643 := by
  apply lucas_primality 5897562454643 (2 : ZMod 5897562454643)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2948781227321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2948781227321, 1)] : List FactorBlock).map factorBlockValue).prod) = 5897562454643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_2948781227321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5897562454643) ^ 2948781227321 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5897562454643) ^ 2 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_7503900605273 : Nat.Prime 7503900605273 := by
  apply lucas_primality 7503900605273 (3 : ZMod 7503900605273)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (937987575659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (937987575659, 1)] : List FactorBlock).map factorBlockValue).prod) = 7503900605273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_937987575659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 7503900605273) ^ 3751950302636 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 7503900605273) ^ 8 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_16635325813163 : Nat.Prime 16635325813163 := by
  apply lucas_primality 16635325813163 (2 : ZMod 16635325813163)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (38371, 1), (30967073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (38371, 1), (30967073, 1)] : List FactorBlock).map factorBlockValue).prod) = 16635325813163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_38371
      · exact prime_oneHundredFortyTwoEJ_30967073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16635325813163) ^ 8317662906581 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 16635325813163) ^ 2376475116166 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 16635325813163) ^ 433539022 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 16635325813163) ^ 537194 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_33559898748209 : Nat.Prime 33559898748209 := by
  apply lucas_primality 33559898748209 (3 : ZMod 33559898748209)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (19, 1), (359, 1), (373, 1), (117773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (19, 1), (359, 1), (373, 1), (117773, 1)] : List FactorBlock).map factorBlockValue).prod) = 33559898748209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_359
      · exact prime_oneHundredFortyTwoEJ_373
      · exact prime_oneHundredFortyTwoEJ_117773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33559898748209) ^ 16779949374104 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33559898748209) ^ 4794271249744 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33559898748209) ^ 1766310460432 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33559898748209) ^ 93481612112 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33559898748209) ^ 89972918896 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 33559898748209) ^ 284954096 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_34040597569889 : Nat.Prime 34040597569889 := by
  apply lucas_primality 34040597569889 (6 : ZMod 34040597569889)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (13, 1), (1031, 1), (11338279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (13, 1), (1031, 1), (11338279, 1)] : List FactorBlock).map factorBlockValue).prod) = 34040597569889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_1031
      · exact prime_oneHundredFortyTwoEJ_11338279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 34040597569889) ^ 17020298784944 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 34040597569889) ^ 4862942509984 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 34040597569889) ^ 2618507505376 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 34040597569889) ^ 33017068448 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 34040597569889) ^ 3002272 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_59342567506567 : Nat.Prime 59342567506567 := by
  apply lucas_primality 59342567506567 (3 : ZMod 59342567506567)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (631, 1), (15674212231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (631, 1), (15674212231, 1)] : List FactorBlock).map factorBlockValue).prod) = 59342567506567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_631
      · exact prime_oneHundredFortyTwoEJ_15674212231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59342567506567) ^ 29671283753283 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59342567506567) ^ 19780855835522 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59342567506567) ^ 94045273386 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 59342567506567) ^ 3786 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_63976856057017 : Nat.Prime 63976856057017 := by
  apply lucas_primality 63976856057017 (10 : ZMod 63976856057017)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (380814619387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (380814619387, 1)] : List FactorBlock).map factorBlockValue).prod) = 63976856057017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_380814619387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 63976856057017) ^ 31988428028508 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 63976856057017) ^ 21325618685672 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 63976856057017) ^ 9139550865288 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 63976856057017) ^ 168 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_65360953972751 : Nat.Prime 65360953972751 := by
  apply lucas_primality 65360953972751 (13 : ZMod 65360953972751)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (261443815891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (261443815891, 1)] : List FactorBlock).map factorBlockValue).prod) = 65360953972751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_261443815891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 65360953972751) ^ 32680476986375 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 65360953972751) ^ 13072190794550 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 65360953972751) ^ 250 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_76236884035267 : Nat.Prime 76236884035267 := by
  apply lucas_primality 76236884035267 (7 : ZMod 76236884035267)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (85276156639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (85276156639, 1)] : List FactorBlock).map factorBlockValue).prod) = 76236884035267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_149
      · exact prime_oneHundredFortyTwoEJ_85276156639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 76236884035267) ^ 38118442017633 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 76236884035267) ^ 25412294678422 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 76236884035267) ^ 511656939834 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 76236884035267) ^ 894 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_89236111517831 : Nat.Prime 89236111517831 := by
  apply lucas_primality 89236111517831 (13 : ZMod 89236111517831)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1777, 1), (7603, 1), (660493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1777, 1), (7603, 1), (660493, 1)] : List FactorBlock).map factorBlockValue).prod) = 89236111517831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_1777
      · exact prime_oneHundredFortyTwoEJ_7603
      · exact prime_oneHundredFortyTwoEJ_660493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 89236111517831) ^ 44618055758915 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 89236111517831) ^ 17847222303566 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 89236111517831) ^ 50217282790 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 89236111517831) ^ 11736960610 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 89236111517831) ^ 135105310 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_91966475174689 : Nat.Prime 91966475174689 := by
  apply lucas_primality 91966475174689 (7 : ZMod 91966475174689)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (797, 1), (400662533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (797, 1), (400662533, 1)] : List FactorBlock).map factorBlockValue).prod) = 91966475174689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_797
      · exact prime_oneHundredFortyTwoEJ_400662533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 91966475174689) ^ 45983237587344 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 91966475174689) ^ 30655491724896 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 91966475174689) ^ 115390809504 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 91966475174689) ^ 229536 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_100425887423209 : Nat.Prime 100425887423209 := by
  apply lucas_primality 100425887423209 (7 : ZMod 100425887423209)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (107, 1), (503, 1), (2551, 1), (10159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (107, 1), (503, 1), (2551, 1), (10159, 1)] : List FactorBlock).map factorBlockValue).prod) = 100425887423209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_107
      · exact prime_oneHundredFortyTwoEJ_503
      · exact prime_oneHundredFortyTwoEJ_2551
      · exact prime_oneHundredFortyTwoEJ_10159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 100425887423209) ^ 50212943711604 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 100425887423209) ^ 33475295807736 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 100425887423209) ^ 938559695544 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 100425887423209) ^ 199653851736 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 100425887423209) ^ 39367262808 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 100425887423209) ^ 9885410712 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_134225379459077 : Nat.Prime 134225379459077 := by
  apply lucas_primality 134225379459077 (2 : ZMod 134225379459077)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (296958804113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (296958804113, 1)] : List FactorBlock).map factorBlockValue).prod) = 134225379459077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_113
      · exact prime_oneHundredFortyTwoEJ_296958804113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 134225379459077) ^ 67112689729538 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 134225379459077) ^ 1187835216452 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 134225379459077) ^ 452 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_168685968830471 : Nat.Prime 168685968830471 := by
  apply lucas_primality 168685968830471 (7 : ZMod 168685968830471)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (185369196517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (185369196517, 1)] : List FactorBlock).map factorBlockValue).prod) = 168685968830471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_185369196517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 168685968830471) ^ 84342984415235 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 168685968830471) ^ 33737193766094 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 168685968830471) ^ 24097995547210 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 168685968830471) ^ 12975843756190 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 168685968830471) ^ 910 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_231262898797543 : Nat.Prime 231262898797543 := by
  apply lucas_primality 231262898797543 (5 : ZMod 231262898797543)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2580443, 1), (14936899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2580443, 1), (14936899, 1)] : List FactorBlock).map factorBlockValue).prod) = 231262898797543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_2580443
      · exact prime_oneHundredFortyTwoEJ_14936899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 231262898797543) ^ 115631449398771 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 231262898797543) ^ 77087632932514 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 231262898797543) ^ 89621394 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 231262898797543) ^ 15482658 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_320598583070543 : Nat.Prime 320598583070543 := by
  apply lucas_primality 320598583070543 (5 : ZMod 320598583070543)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (995647773511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (995647773511, 1)] : List FactorBlock).map factorBlockValue).prod) = 320598583070543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_995647773511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 320598583070543) ^ 160299291535271 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 320598583070543) ^ 45799797581506 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 320598583070543) ^ 13939068829154 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 320598583070543) ^ 322 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_404181720682937 : Nat.Prime 404181720682937 := by
  apply lucas_primality 404181720682937 (3 : ZMod 404181720682937)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (37, 1), (38287, 1), (5094899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (37, 1), (38287, 1), (5094899, 1)] : List FactorBlock).map factorBlockValue).prod) = 404181720682937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_37
      · exact prime_oneHundredFortyTwoEJ_38287
      · exact prime_oneHundredFortyTwoEJ_5094899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 404181720682937) ^ 202090860341468 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 404181720682937) ^ 57740245811848 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 404181720682937) ^ 10923830288728 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 404181720682937) ^ 10556630728 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 404181720682937) ^ 79330664 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_490849005230191 : Nat.Prime 490849005230191 := by
  apply lucas_primality 490849005230191 (6 : ZMod 490849005230191)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (287046201889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (287046201889, 1)] : List FactorBlock).map factorBlockValue).prod) = 490849005230191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_287046201889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 490849005230191) ^ 245424502615095 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 490849005230191) ^ 163616335076730 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 490849005230191) ^ 98169801046038 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 490849005230191) ^ 25834158170010 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 490849005230191) ^ 1710 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_506220017507513 : Nat.Prime 506220017507513 := by
  apply lucas_primality 506220017507513 (3 : ZMod 506220017507513)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (821785742707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (821785742707, 1)] : List FactorBlock).map factorBlockValue).prod) = 506220017507513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_821785742707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 506220017507513) ^ 253110008753756 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 506220017507513) ^ 72317145358216 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 506220017507513) ^ 46020001591592 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 506220017507513) ^ 616 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_534517195034513 : Nat.Prime 534517195034513 := by
  apply lucas_primality 534517195034513 (3 : ZMod 534517195034513)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2411, 1), (14051, 1), (986137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2411, 1), (14051, 1), (986137, 1)] : List FactorBlock).map factorBlockValue).prod) = 534517195034513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_2411
      · exact prime_oneHundredFortyTwoEJ_14051
      · exact prime_oneHundredFortyTwoEJ_986137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 534517195034513) ^ 267258597517256 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 534517195034513) ^ 221699375792 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 534517195034513) ^ 38041220912 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 534517195034513) ^ 542031376 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_764060442704599 : Nat.Prime 764060442704599 := by
  apply lucas_primality 764060442704599 (3 : ZMod 764060442704599)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 1), (2081, 2), (98347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 1), (2081, 2), (98347, 1)] : List FactorBlock).map factorBlockValue).prod) = 764060442704599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_2081
      · exact prime_oneHundredFortyTwoEJ_98347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 764060442704599) ^ 382030221352299 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 764060442704599) ^ 254686814234866 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 764060442704599) ^ 58773880208046 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 764060442704599) ^ 33220019248026 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 764060442704599) ^ 367160231958 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 764060442704599) ^ 7769026434 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_838872702985453 : Nat.Prime 838872702985453 := by
  apply lucas_primality 838872702985453 (5 : ZMod 838872702985453)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3881, 1), (18012383041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3881, 1), (18012383041, 1)] : List FactorBlock).map factorBlockValue).prod) = 838872702985453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_3881
      · exact prime_oneHundredFortyTwoEJ_18012383041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 838872702985453) ^ 419436351492726 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 838872702985453) ^ 279624234328484 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 838872702985453) ^ 216148596492 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 838872702985453) ^ 46572 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1070823646938373 : Nat.Prime 1070823646938373 := by
  apply lucas_primality 1070823646938373 (5 : ZMod 1070823646938373)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2689, 1), (33185311979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2689, 1), (33185311979, 1)] : List FactorBlock).map factorBlockValue).prod) = 1070823646938373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_2689
      · exact prime_oneHundredFortyTwoEJ_33185311979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1070823646938373) ^ 535411823469186 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1070823646938373) ^ 356941215646124 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1070823646938373) ^ 398223743748 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1070823646938373) ^ 32268 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2505943726585591 : Nat.Prime 2505943726585591 := by
  apply lucas_primality 2505943726585591 (3 : ZMod 2505943726585591)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (137, 1), (457, 1), (1334176517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (137, 1), (457, 1), (1334176517, 1)] : List FactorBlock).map factorBlockValue).prod) = 2505943726585591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_137
      · exact prime_oneHundredFortyTwoEJ_457
      · exact prime_oneHundredFortyTwoEJ_1334176517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2505943726585591) ^ 1252971863292795 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505943726585591) ^ 835314575528530 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505943726585591) ^ 501188745317118 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505943726585591) ^ 18291560048070 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505943726585591) ^ 5483465484870 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505943726585591) ^ 1878270 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3215477069527031 : Nat.Prime 3215477069527031 := by
  apply lucas_primality 3215477069527031 (7 : ZMod 3215477069527031)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (127, 1), (32881450757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (127, 1), (32881450757, 1)] : List FactorBlock).map factorBlockValue).prod) = 3215477069527031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_127
      · exact prime_oneHundredFortyTwoEJ_32881450757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3215477069527031) ^ 1607738534763515 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3215477069527031) ^ 643095413905406 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3215477069527031) ^ 459353867075290 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3215477069527031) ^ 292316097229730 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3215477069527031) ^ 25318717082890 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 3215477069527031) ^ 97790 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_5002455424617757 : Nat.Prime 5002455424617757 := by
  apply lucas_primality 5002455424617757 (2 : ZMod 5002455424617757)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (541, 1), (36693185933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (541, 1), (36693185933, 1)] : List FactorBlock).map factorBlockValue).prod) = 5002455424617757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_541
      · exact prime_oneHundredFortyTwoEJ_36693185933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5002455424617757) ^ 2501227712308878 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5002455424617757) ^ 1667485141539252 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5002455424617757) ^ 714636489231108 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5002455424617757) ^ 9246682855116 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5002455424617757) ^ 136332 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_6376544700516061 : Nat.Prime 6376544700516061 := by
  apply lucas_primality 6376544700516061 (6 : ZMod 6376544700516061)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (10133, 1), (1498297571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (10133, 1), (1498297571, 1)] : List FactorBlock).map factorBlockValue).prod) = 6376544700516061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_10133
      · exact prime_oneHundredFortyTwoEJ_1498297571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6376544700516061) ^ 3188272350258030 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 6376544700516061) ^ 2125514900172020 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 6376544700516061) ^ 1275308940103212 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 6376544700516061) ^ 910934957216580 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 6376544700516061) ^ 629284979820 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 6376544700516061) ^ 4255860 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_8193176549514251 : Nat.Prime 8193176549514251 := by
  apply lucas_primality 8193176549514251 (2 : ZMod 8193176549514251)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (128389, 1), (36465859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (128389, 1), (36465859, 1)] : List FactorBlock).map factorBlockValue).prod) = 8193176549514251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_128389
      · exact prime_oneHundredFortyTwoEJ_36465859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8193176549514251) ^ 4096588274757125 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8193176549514251) ^ 1638635309902850 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8193176549514251) ^ 1170453792787750 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8193176549514251) ^ 63815253250 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8193176549514251) ^ 224680750 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_10845995841706573 : Nat.Prime 10845995841706573 := by
  apply lucas_primality 10845995841706573 (6 : ZMod 10845995841706573)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (100425887423209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (100425887423209, 1)] : List FactorBlock).map factorBlockValue).prod) = 10845995841706573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_100425887423209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 10845995841706573) ^ 5422997920853286 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 10845995841706573) ^ 3615331947235524 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 10845995841706573) ^ 108 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_11227840236568807 : Nat.Prime 11227840236568807 := by
  apply lucas_primality 11227840236568807 (3 : ZMod 11227840236568807)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (89, 1), (678255420839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (89, 1), (678255420839, 1)] : List FactorBlock).map factorBlockValue).prod) = 11227840236568807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_89
      · exact prime_oneHundredFortyTwoEJ_678255420839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11227840236568807) ^ 5613920118284403 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11227840236568807) ^ 3742613412189602 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11227840236568807) ^ 362188394728026 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11227840236568807) ^ 126155508276054 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11227840236568807) ^ 16554 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_13899355741773911 : Nat.Prime 13899355741773911 := by
  apply lucas_primality 13899355741773911 (13 : ZMod 13899355741773911)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (83, 1), (607, 1), (27588487211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (83, 1), (607, 1), (27588487211, 1)] : List FactorBlock).map factorBlockValue).prod) = 13899355741773911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_83
      · exact prime_oneHundredFortyTwoEJ_607
      · exact prime_oneHundredFortyTwoEJ_27588487211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 13899355741773911) ^ 6949677870886955 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 13899355741773911) ^ 2779871148354782 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 13899355741773911) ^ 167462117370770 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 13899355741773911) ^ 22898444385130 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 13899355741773911) ^ 503810 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_17429006512074973 : Nat.Prime 17429006512074973 := by
  apply lucas_primality 17429006512074973 (2 : ZMod 17429006512074973)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1217, 1), (27431, 1), (43507003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1217, 1), (27431, 1), (43507003, 1)] : List FactorBlock).map factorBlockValue).prod) = 17429006512074973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_1217
      · exact prime_oneHundredFortyTwoEJ_27431
      · exact prime_oneHundredFortyTwoEJ_43507003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17429006512074973) ^ 8714503256037486 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17429006512074973) ^ 5809668837358324 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17429006512074973) ^ 14321287191516 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17429006512074973) ^ 635376271812 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17429006512074973) ^ 400602324 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_26803385787191851 : Nat.Prime 26803385787191851 := by
  apply lucas_primality 26803385787191851 (2 : ZMod 26803385787191851)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (37907, 1), (1571294999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (37907, 1), (1571294999, 1)] : List FactorBlock).map factorBlockValue).prod) = 26803385787191851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_37907
      · exact prime_oneHundredFortyTwoEJ_1571294999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26803385787191851) ^ 13401692893595925 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 26803385787191851) ^ 8934461929063950 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 26803385787191851) ^ 5360677157438370 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 26803385787191851) ^ 707082749550 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 26803385787191851) ^ 17058150 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_26988512256723821 : Nat.Prime 26988512256723821 := by
  apply lucas_primality 26988512256723821 (2 : ZMod 26988512256723821)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (19, 1), (641, 1), (2393, 1), (4209223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (19, 1), (641, 1), (2393, 1), (4209223, 1)] : List FactorBlock).map factorBlockValue).prod) = 26988512256723821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_641
      · exact prime_oneHundredFortyTwoEJ_2393
      · exact prime_oneHundredFortyTwoEJ_4209223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26988512256723821) ^ 13494256128361910 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 26988512256723821) ^ 5397702451344764 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 26988512256723821) ^ 2453501114247620 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 26988512256723821) ^ 1420448013511780 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 26988512256723821) ^ 42103763271020 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 26988512256723821) ^ 11278107921740 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 26988512256723821) ^ 6411756340 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_29287693336184641 : Nat.Prime 29287693336184641 := by
  apply lucas_primality 29287693336184641 (11 : ZMod 29287693336184641)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (7, 1), (1452762566279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (7, 1), (1452762566279, 1)] : List FactorBlock).map factorBlockValue).prod) = 29287693336184641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_1452762566279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 29287693336184641) ^ 14643846668092320 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 29287693336184641) ^ 9762564445394880 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 29287693336184641) ^ 5857538667236928 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 29287693336184641) ^ 4183956190883520 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 29287693336184641) ^ 20160 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_32855358051929137 : Nat.Prime 32855358051929137 := by
  apply lucas_primality 32855358051929137 (10 : ZMod 32855358051929137)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (73, 1), (433, 1), (21654801673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (73, 1), (433, 1), (21654801673, 1)] : List FactorBlock).map factorBlockValue).prod) = 32855358051929137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_73
      · exact prime_oneHundredFortyTwoEJ_433
      · exact prime_oneHundredFortyTwoEJ_21654801673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32855358051929137) ^ 16427679025964568 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 32855358051929137) ^ 10951786017309712 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 32855358051929137) ^ 450073397971632 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 32855358051929137) ^ 75878425062192 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 32855358051929137) ^ 1517232 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_58809622940938231 : Nat.Prime 58809622940938231 := by
  apply lucas_primality 58809622940938231 (6 : ZMod 58809622940938231)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (28729, 1), (68234911229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (28729, 1), (68234911229, 1)] : List FactorBlock).map factorBlockValue).prod) = 58809622940938231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_28729
      · exact prime_oneHundredFortyTwoEJ_68234911229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 58809622940938231) ^ 29404811470469115 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 58809622940938231) ^ 19603207646979410 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 58809622940938231) ^ 11761924588187646 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 58809622940938231) ^ 2047047336870 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 58809622940938231) ^ 861870 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_104574039072449839 : Nat.Prime 104574039072449839 := by
  apply lucas_primality 104574039072449839 (3 : ZMod 104574039072449839)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17429006512074973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17429006512074973, 1)] : List FactorBlock).map factorBlockValue).prod) = 104574039072449839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_17429006512074973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 104574039072449839) ^ 52287019536224919 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 104574039072449839) ^ 34858013024149946 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 104574039072449839) ^ 6 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_156788119500149519 : Nat.Prime 156788119500149519 := by
  apply lucas_primality 156788119500149519 (7 : ZMod 156788119500149519)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (47, 1), (317, 1), (58901, 1), (3883967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (47, 1), (317, 1), (58901, 1), (3883967, 1)] : List FactorBlock).map factorBlockValue).prod) = 156788119500149519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_47
      · exact prime_oneHundredFortyTwoEJ_317
      · exact prime_oneHundredFortyTwoEJ_58901
      · exact prime_oneHundredFortyTwoEJ_3883967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 156788119500149519) ^ 78394059750074759 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 156788119500149519) ^ 6816874760876066 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 156788119500149519) ^ 3335917436173394 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 156788119500149519) ^ 494599746057254 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 156788119500149519) ^ 2661892319318 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 156788119500149519) ^ 40368035954 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_170711407936764193 : Nat.Prime 170711407936764193 := by
  apply lucas_primality 170711407936764193 (13 : ZMod 170711407936764193)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1103, 1), (1612188424909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1103, 1), (1612188424909, 1)] : List FactorBlock).map factorBlockValue).prod) = 170711407936764193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_1103
      · exact prime_oneHundredFortyTwoEJ_1612188424909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 170711407936764193) ^ 85355703968382096 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 170711407936764193) ^ 56903802645588064 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 170711407936764193) ^ 154770088791264 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 170711407936764193) ^ 105888 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_177856633274990129 : Nat.Prime 177856633274990129 := by
  apply lucas_primality 177856633274990129 (3 : ZMod 177856633274990129)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (97, 1), (9311, 1), (110233, 1), (111653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (97, 1), (9311, 1), (110233, 1), (111653, 1)] : List FactorBlock).map factorBlockValue).prod) = 177856633274990129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_97
      · exact prime_oneHundredFortyTwoEJ_9311
      · exact prime_oneHundredFortyTwoEJ_110233
      · exact prime_oneHundredFortyTwoEJ_111653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 177856633274990129) ^ 88928316637495064 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 177856633274990129) ^ 1833573538917424 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 177856633274990129) ^ 19101775671248 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 177856633274990129) ^ 1613460880816 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 177856633274990129) ^ 1592940926576 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_371598660635984011 : Nat.Prime 371598660635984011 := by
  apply lucas_primality 371598660635984011 (3 : ZMod 371598660635984011)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (31, 1), (151, 1), (882049563569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (31, 1), (151, 1), (882049563569, 1)] : List FactorBlock).map factorBlockValue).prod) = 371598660635984011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_151
      · exact prime_oneHundredFortyTwoEJ_882049563569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 371598660635984011) ^ 185799330317992005 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 371598660635984011) ^ 123866220211994670 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 371598660635984011) ^ 74319732127196802 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 371598660635984011) ^ 11987053568902710 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 371598660635984011) ^ 2460918282357510 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 371598660635984011) ^ 421290 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_448641709958060071 : Nat.Prime 448641709958060071 := by
  apply lucas_primality 448641709958060071 (6 : ZMod 448641709958060071)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (404181720682937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (404181720682937, 1)] : List FactorBlock).map factorBlockValue).prod) = 448641709958060071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_37
      · exact prime_oneHundredFortyTwoEJ_404181720682937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 448641709958060071) ^ 224320854979030035 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 448641709958060071) ^ 149547236652686690 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 448641709958060071) ^ 89728341991612014 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 448641709958060071) ^ 12125451620488110 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 448641709958060071) ^ 1110 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_484252315524528977 : Nat.Prime 484252315524528977 := by
  apply lucas_primality 484252315524528977 (3 : ZMod 484252315524528977)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (73, 1), (670223, 1), (618599459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (73, 1), (670223, 1), (618599459, 1)] : List FactorBlock).map factorBlockValue).prod) = 484252315524528977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_73
      · exact prime_oneHundredFortyTwoEJ_670223
      · exact prime_oneHundredFortyTwoEJ_618599459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 484252315524528977) ^ 242126157762264488 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 484252315524528977) ^ 6633593363349712 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 484252315524528977) ^ 722524168112 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 484252315524528977) ^ 782820464 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_543933858961233823 : Nat.Prime 543933858961233823 := by
  apply lucas_primality 543933858961233823 (3 : ZMod 543933858961233823)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (73, 1), (65360953972751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (73, 1), (65360953972751, 1)] : List FactorBlock).map factorBlockValue).prod) = 543933858961233823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_73
      · exact prime_oneHundredFortyTwoEJ_65360953972751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 543933858961233823) ^ 271966929480616911 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 543933858961233823) ^ 181311286320411274 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 543933858961233823) ^ 28628097840064938 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 543933858961233823) ^ 7451148752893614 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 543933858961233823) ^ 8322 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_589674487318220723 : Nat.Prime 589674487318220723 := by
  apply lucas_primality 589674487318220723 (2 : ZMod 589674487318220723)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (26803385787191851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (26803385787191851, 1)] : List FactorBlock).map factorBlockValue).prod) = 589674487318220723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_26803385787191851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 589674487318220723) ^ 294837243659110361 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 589674487318220723) ^ 53606771574383702 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 589674487318220723) ^ 22 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_616865144496483667 : Nat.Prime 616865144496483667 := by
  apply lucas_primality 616865144496483667 (2 : ZMod 616865144496483667)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (67, 1), (26357, 1), (8317066267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (67, 1), (26357, 1), (8317066267, 1)] : List FactorBlock).map factorBlockValue).prod) = 616865144496483667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_67
      · exact prime_oneHundredFortyTwoEJ_26357
      · exact prime_oneHundredFortyTwoEJ_8317066267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 616865144496483667) ^ 308432572248241833 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 616865144496483667) ^ 205621714832161222 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 616865144496483667) ^ 88123592070926238 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 616865144496483667) ^ 9206942455171398 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 616865144496483667) ^ 23404224475338 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 616865144496483667) ^ 74168598 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_626302248844999291 : Nat.Prime 626302248844999291 := by
  apply lucas_primality 626302248844999291 (2 : ZMod 626302248844999291)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (821, 1), (16141, 1), (68495381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (821, 1), (16141, 1), (68495381, 1)] : List FactorBlock).map factorBlockValue).prod) = 626302248844999291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_821
      · exact prime_oneHundredFortyTwoEJ_16141
      · exact prime_oneHundredFortyTwoEJ_68495381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 626302248844999291) ^ 313151124422499645 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 626302248844999291) ^ 208767416281666430 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 626302248844999291) ^ 125260449768999858 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 626302248844999291) ^ 27230532558478230 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 626302248844999291) ^ 762852921857490 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 626302248844999291) ^ 38801948382690 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 626302248844999291) ^ 9143715090 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_627658986764630603 : Nat.Prime 627658986764630603 := by
  apply lucas_primality 627658986764630603 (2 : ZMod 627658986764630603)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (184721587, 1), (1698932423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (184721587, 1), (1698932423, 1)] : List FactorBlock).map factorBlockValue).prod) = 627658986764630603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_184721587
      · exact prime_oneHundredFortyTwoEJ_1698932423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 627658986764630603) ^ 313829493382315301 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 627658986764630603) ^ 3397864846 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 627658986764630603) ^ 369443174 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_653086426204261433 : Nat.Prime 653086426204261433 := by
  apply lucas_primality 653086426204261433 (3 : ZMod 653086426204261433)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (353, 1), (231262898797543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (353, 1), (231262898797543, 1)] : List FactorBlock).map factorBlockValue).prod) = 653086426204261433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_353
      · exact prime_oneHundredFortyTwoEJ_231262898797543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 653086426204261433) ^ 326543213102130716 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 653086426204261433) ^ 1850103190380344 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 653086426204261433) ^ 2824 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_907524751651510081 : Nat.Prime 907524751651510081 := by
  apply lucas_primality 907524751651510081 (14 : ZMod 907524751651510081)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (11, 1), (197, 1), (877, 1), (497426297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (11, 1), (197, 1), (877, 1), (497426297, 1)] : List FactorBlock).map factorBlockValue).prod) = 907524751651510081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_197
      · exact prime_oneHundredFortyTwoEJ_877
      · exact prime_oneHundredFortyTwoEJ_497426297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 907524751651510081) ^ 453762375825755040 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 907524751651510081) ^ 302508250550503360 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 907524751651510081) ^ 181504950330302016 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 907524751651510081) ^ 82502250150137280 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 907524751651510081) ^ 4606724627672640 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 907524751651510081) ^ 1034805874175040 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (14 : ZMod 907524751651510081) ^ 1824440640 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1822221349367422937 : Nat.Prime 1822221349367422937 := by
  apply lucas_primality 1822221349367422937 (3 : ZMod 1822221349367422937)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (820921, 1), (277466003027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (820921, 1), (277466003027, 1)] : List FactorBlock).map factorBlockValue).prod) = 1822221349367422937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_820921
      · exact prime_oneHundredFortyTwoEJ_277466003027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1822221349367422937) ^ 911110674683711468 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1822221349367422937) ^ 2219728024216 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1822221349367422937) ^ 6567368 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_101
      · exact prime_oneHundredFortyTwoEJ_191
      · exact prime_oneHundredFortyTwoEJ_48017
      · exact prime_oneHundredFortyTwoEJ_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2974243683278288063 : Nat.Prime 2974243683278288063 := by
  apply lucas_primality 2974243683278288063 (5 : ZMod 2974243683278288063)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (734535481, 1), (2024574551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (734535481, 1), (2024574551, 1)] : List FactorBlock).map factorBlockValue).prod) = 2974243683278288063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_734535481
      · exact prime_oneHundredFortyTwoEJ_2024574551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2974243683278288063) ^ 1487121841639144031 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2974243683278288063) ^ 4049149102 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2974243683278288063) ^ 1469070962 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3091803919620771983 : Nat.Prime 3091803919620771983 := by
  apply lucas_primality 3091803919620771983 (5 : ZMod 3091803919620771983)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1031, 1), (9057431, 1), (15049621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1031, 1), (9057431, 1), (15049621, 1)] : List FactorBlock).map factorBlockValue).prod) = 3091803919620771983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_1031
      · exact prime_oneHundredFortyTwoEJ_9057431
      · exact prime_oneHundredFortyTwoEJ_15049621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3091803919620771983) ^ 1545901959810385991 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3091803919620771983) ^ 281073083601888362 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3091803919620771983) ^ 2998839883240322 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3091803919620771983) ^ 341355503522 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3091803919620771983) ^ 205440649942 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3529379692505299981 : Nat.Prime 3529379692505299981 := by
  apply lucas_primality 3529379692505299981 (6 : ZMod 3529379692505299981)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (20984779, 1), (2803126727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (20984779, 1), (2803126727, 1)] : List FactorBlock).map factorBlockValue).prod) = 3529379692505299981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_20984779
      · exact prime_oneHundredFortyTwoEJ_2803126727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3529379692505299981) ^ 1764689846252649990 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3529379692505299981) ^ 1176459897501766660 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3529379692505299981) ^ 705875938501059996 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3529379692505299981) ^ 168187603620 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 3529379692505299981) ^ 1259086740 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3757813493069995747 : Nat.Prime 3757813493069995747 := by
  apply lucas_primality 3757813493069995747 (3 : ZMod 3757813493069995747)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (626302248844999291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (626302248844999291, 1)] : List FactorBlock).map factorBlockValue).prod) = 3757813493069995747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_626302248844999291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3757813493069995747) ^ 1878906746534997873 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3757813493069995747) ^ 1252604497689998582 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3757813493069995747) ^ 6 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3882232783126286653 : Nat.Prime 3882232783126286653 := by
  apply lucas_primality 3882232783126286653 (2 : ZMod 3882232783126286653)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (307, 1), (773, 1), (3803, 1), (51210391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (307, 1), (773, 1), (3803, 1), (51210391, 1)] : List FactorBlock).map factorBlockValue).prod) = 3882232783126286653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_307
      · exact prime_oneHundredFortyTwoEJ_773
      · exact prime_oneHundredFortyTwoEJ_3803
      · exact prime_oneHundredFortyTwoEJ_51210391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3882232783126286653) ^ 1941116391563143326 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3882232783126286653) ^ 1294077594375428884 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3882232783126286653) ^ 554604683303755236 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3882232783126286653) ^ 12645709391290836 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3882232783126286653) ^ 5022293380499724 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3882232783126286653) ^ 1020834284282484 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3882232783126286653) ^ 75809473572 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3989887441480325969 : Nat.Prime 3989887441480325969 := by
  apply lucas_primality 3989887441480325969 (3 : ZMod 3989887441480325969)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (107, 1), (4021, 1), (52690233769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (107, 1), (4021, 1), (52690233769, 1)] : List FactorBlock).map factorBlockValue).prod) = 3989887441480325969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_107
      · exact prime_oneHundredFortyTwoEJ_4021
      · exact prime_oneHundredFortyTwoEJ_52690233769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3989887441480325969) ^ 1994943720740162984 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3989887441480325969) ^ 362717040134575088 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3989887441480325969) ^ 37288667677386224 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3989887441480325969) ^ 992262482337808 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3989887441480325969) ^ 75723472 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_4386958645490472043 : Nat.Prime 4386958645490472043 := by
  apply lucas_primality 4386958645490472043 (2 : ZMod 4386958645490472043)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 2), (59342567506567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 2), (59342567506567, 1)] : List FactorBlock).map factorBlockValue).prod) = 4386958645490472043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_37
      · exact prime_oneHundredFortyTwoEJ_59342567506567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4386958645490472043) ^ 2193479322745236021 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4386958645490472043) ^ 1462319548496824014 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4386958645490472043) ^ 118566449878120866 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4386958645490472043) ^ 73926 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_5621009223087344087 : Nat.Prime 5621009223087344087 := by
  apply lucas_primality 5621009223087344087 (5 : ZMod 5621009223087344087)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (13, 1), (3271, 1), (132859, 1), (6460687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (13, 1), (3271, 1), (132859, 1), (6460687, 1)] : List FactorBlock).map factorBlockValue).prod) = 5621009223087344087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_3271
      · exact prime_oneHundredFortyTwoEJ_132859
      · exact prime_oneHundredFortyTwoEJ_6460687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5621009223087344087) ^ 2810504611543672043 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5621009223087344087) ^ 803001317583906298 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5621009223087344087) ^ 511000838462485826 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5621009223087344087) ^ 432385324852872622 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5621009223087344087) ^ 1718437549094266 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5621009223087344087) ^ 42308080168354 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5621009223087344087) ^ 870032741578 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_5975856279431873119 : Nat.Prime 5975856279431873119 := by
  apply lucas_primality 5975856279431873119 (6 : ZMod 5975856279431873119)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (41, 1), (6470839, 1), (417120883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (41, 1), (6470839, 1), (417120883, 1)] : List FactorBlock).map factorBlockValue).prod) = 5975856279431873119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_41
      · exact prime_oneHundredFortyTwoEJ_6470839
      · exact prime_oneHundredFortyTwoEJ_417120883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5975856279431873119) ^ 2987928139715936559 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 5975856279431873119) ^ 1991952093143957706 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 5975856279431873119) ^ 145752592181265198 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 5975856279431873119) ^ 923505634962 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 5975856279431873119) ^ 14326437546 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_6134271843075769199 : Nat.Prime 6134271843075769199 := by
  apply lucas_primality 6134271843075769199 (7 : ZMod 6134271843075769199)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (251, 1), (18169, 1), (51735056017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (251, 1), (18169, 1), (51735056017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6134271843075769199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_251
      · exact prime_oneHundredFortyTwoEJ_18169
      · exact prime_oneHundredFortyTwoEJ_51735056017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6134271843075769199) ^ 3067135921537884599 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6134271843075769199) ^ 471867064851982246 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6134271843075769199) ^ 24439330052094698 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6134271843075769199) ^ 337622975566942 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 6134271843075769199) ^ 118570894 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_6977614958096236793 : Nat.Prime 6977614958096236793 := by
  apply lucas_primality 6977614958096236793 (3 : ZMod 6977614958096236793)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (127, 1), (22643, 1), (27077, 1), (861659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (127, 1), (22643, 1), (27077, 1), (861659, 1)] : List FactorBlock).map factorBlockValue).prod) = 6977614958096236793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_127
      · exact prime_oneHundredFortyTwoEJ_22643
      · exact prime_oneHundredFortyTwoEJ_27077
      · exact prime_oneHundredFortyTwoEJ_861659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6977614958096236793) ^ 3488807479048118396 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6977614958096236793) ^ 536739612161248984 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6977614958096236793) ^ 54941850063749896 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6977614958096236793) ^ 308157706933544 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6977614958096236793) ^ 257695274886296 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6977614958096236793) ^ 8097884381288 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_8671091072656451833 : Nat.Prime 8671091072656451833 := by
  apply lucas_primality 8671091072656451833 (5 : ZMod 8671091072656451833)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (557, 1), (2561749, 1), (28133789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (557, 1), (2561749, 1), (28133789, 1)] : List FactorBlock).map factorBlockValue).prod) = 8671091072656451833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_557
      · exact prime_oneHundredFortyTwoEJ_2561749
      · exact prime_oneHundredFortyTwoEJ_28133789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8671091072656451833) ^ 4335545536328225916 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8671091072656451833) ^ 2890363690885483944 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8671091072656451833) ^ 15567488460783576 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8671091072656451833) ^ 3384832422168 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 8671091072656451833) ^ 308209145688 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_10192728026288091491 : Nat.Prime 10192728026288091491 := by
  apply lucas_primality 10192728026288091491 (2 : ZMod 10192728026288091491)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (31, 1), (677, 1), (63929, 1), (44688239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (31, 1), (677, 1), (63929, 1), (44688239, 1)] : List FactorBlock).map factorBlockValue).prod) = 10192728026288091491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_677
      · exact prime_oneHundredFortyTwoEJ_63929
      · exact prime_oneHundredFortyTwoEJ_44688239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10192728026288091491) ^ 5096364013144045745 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10192728026288091491) ^ 2038545605257618298 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10192728026288091491) ^ 599572236840475970 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10192728026288091491) ^ 328797678267357790 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10192728026288091491) ^ 15055728251533370 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10192728026288091491) ^ 159438252221810 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10192728026288091491) ^ 228085246910 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_11170354011363935573 : Nat.Prime 11170354011363935573 := by
  apply lucas_primality 11170354011363935573 (2 : ZMod 11170354011363935573)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (82037, 1), (34040597569889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (82037, 1), (34040597569889, 1)] : List FactorBlock).map factorBlockValue).prod) = 11170354011363935573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_82037
      · exact prime_oneHundredFortyTwoEJ_34040597569889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11170354011363935573) ^ 5585177005681967786 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11170354011363935573) ^ 136162390279556 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 11170354011363935573) ^ 328148 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_18274901311213799053 : Nat.Prime 18274901311213799053 := by
  apply lucas_primality 18274901311213799053 (2 : ZMod 18274901311213799053)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2361701, 1), (644835414221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2361701, 1), (644835414221, 1)] : List FactorBlock).map factorBlockValue).prod) = 18274901311213799053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_2361701
      · exact prime_oneHundredFortyTwoEJ_644835414221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18274901311213799053) ^ 9137450655606899526 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18274901311213799053) ^ 6091633770404599684 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18274901311213799053) ^ 7738024970652 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 18274901311213799053) ^ 28340412 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_23537616606092990941 : Nat.Prime 23537616606092990941 := by
  apply lucas_primality 23537616606092990941 (13 : ZMod 23537616606092990941)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (1181, 1), (97151, 1), (44404127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (1181, 1), (97151, 1), (44404127, 1)] : List FactorBlock).map factorBlockValue).prod) = 23537616606092990941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_1181
      · exact prime_oneHundredFortyTwoEJ_97151
      · exact prime_oneHundredFortyTwoEJ_44404127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 23537616606092990941) ^ 11768808303046495470 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 23537616606092990941) ^ 7845872202030996980 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 23537616606092990941) ^ 4707523321218598188 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 23537616606092990941) ^ 3362516658013284420 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 23537616606092990941) ^ 2139783327826635540 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 23537616606092990941) ^ 19930242680857740 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 23537616606092990941) ^ 242278685819940 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 23537616606092990941) ^ 530077229220 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_36242620839285681817 : Nat.Prime 36242620839285681817 := by
  apply lucas_primality 36242620839285681817 (5 : ZMod 36242620839285681817)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (392809, 1), (1281461814467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (392809, 1), (1281461814467, 1)] : List FactorBlock).map factorBlockValue).prod) = 36242620839285681817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_392809
      · exact prime_oneHundredFortyTwoEJ_1281461814467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 36242620839285681817) ^ 18121310419642840908 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 36242620839285681817) ^ 12080873613095227272 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 36242620839285681817) ^ 92265250641624 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 36242620839285681817) ^ 28282248 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_62500858541336471521 : Nat.Prime 62500858541336471521 := by
  apply lucas_primality 62500858541336471521 (7 : ZMod 62500858541336471521)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (11, 1), (29, 1), (6005477, 1), (67968323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (11, 1), (29, 1), (6005477, 1), (67968323, 1)] : List FactorBlock).map factorBlockValue).prod) = 62500858541336471521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_29
      · exact prime_oneHundredFortyTwoEJ_6005477
      · exact prime_oneHundredFortyTwoEJ_67968323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 62500858541336471521) ^ 31250429270668235760 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 62500858541336471521) ^ 20833619513778823840 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 62500858541336471521) ^ 12500171708267294304 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 62500858541336471521) ^ 5681896231030588320 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 62500858541336471521) ^ 2155202018666774880 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 62500858541336471521) ^ 10407309617760 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 62500858541336471521) ^ 919558638240 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_100392172159550072143 : Nat.Prime 100392172159550072143 := by
  apply lucas_primality 100392172159550072143 (3 : ZMod 100392172159550072143)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (251, 1), (1553, 1), (16691, 1), (233791319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (251, 1), (1553, 1), (16691, 1), (233791319, 1)] : List FactorBlock).map factorBlockValue).prod) = 100392172159550072143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_251
      · exact prime_oneHundredFortyTwoEJ_1553
      · exact prime_oneHundredFortyTwoEJ_16691
      · exact prime_oneHundredFortyTwoEJ_233791319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 100392172159550072143) ^ 50196086079775036071 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 100392172159550072143) ^ 33464057386516690714 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 100392172159550072143) ^ 9126561105413642922 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 100392172159550072143) ^ 399968813384661642 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 100392172159550072143) ^ 64644025859336814 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 100392172159550072143) ^ 6014748796330362 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 100392172159550072143) ^ 429409323618 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_104165651384717728783 : Nat.Prime 104165651384717728783 := by
  apply lucas_primality 104165651384717728783 (3 : ZMod 104165651384717728783)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (73, 1), (773, 1), (7503900605273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (73, 1), (773, 1), (7503900605273, 1)] : List FactorBlock).map factorBlockValue).prod) = 104165651384717728783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_41
      · exact prime_oneHundredFortyTwoEJ_73
      · exact prime_oneHundredFortyTwoEJ_773
      · exact prime_oneHundredFortyTwoEJ_7503900605273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 104165651384717728783) ^ 52082825692358864391 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 104165651384717728783) ^ 34721883794905909594 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 104165651384717728783) ^ 2540625643529700702 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 104165651384717728783) ^ 1426926731297503134 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 104165651384717728783) ^ 134755047069492534 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 104165651384717728783) ^ 13881534 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_131070922340106165331 : Nat.Prime 131070922340106165331 := by
  apply lucas_primality 131070922340106165331 (10 : ZMod 131070922340106165331)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (8497033, 1), (514183097167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (8497033, 1), (514183097167, 1)] : List FactorBlock).map factorBlockValue).prod) = 131070922340106165331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_8497033
      · exact prime_oneHundredFortyTwoEJ_514183097167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 131070922340106165331) ^ 65535461170053082665 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 131070922340106165331) ^ 43690307446702055110 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 131070922340106165331) ^ 26214184468021233066 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 131070922340106165331) ^ 15425492915010 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (10 : ZMod 131070922340106165331) ^ 254910990 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_275406941626342132619 : Nat.Prime 275406941626342132619 := by
  apply lucas_primality 275406941626342132619 (2 : ZMod 275406941626342132619)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (14923, 1), (838872702985453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (14923, 1), (838872702985453, 1)] : List FactorBlock).map factorBlockValue).prod) = 275406941626342132619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_14923
      · exact prime_oneHundredFortyTwoEJ_838872702985453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 275406941626342132619) ^ 137703470813171066309 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 275406941626342132619) ^ 25036994693303830238 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 275406941626342132619) ^ 18455199465679966 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 275406941626342132619) ^ 328306 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_775279187947180775633 : Nat.Prime 775279187947180775633 := by
  apply lucas_primality 775279187947180775633 (3 : ZMod 775279187947180775633)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (359, 1), (421, 1), (320598583070543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (359, 1), (421, 1), (320598583070543, 1)] : List FactorBlock).map factorBlockValue).prod) = 775279187947180775633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_359
      · exact prime_oneHundredFortyTwoEJ_421
      · exact prime_oneHundredFortyTwoEJ_320598583070543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 775279187947180775633) ^ 387639593973590387816 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 775279187947180775633) ^ 2159552055563177648 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 775279187947180775633) ^ 1841518261157198992 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 775279187947180775633) ^ 2418224 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1111020430041054511829 : Nat.Prime 1111020430041054511829 := by
  apply lucas_primality 1111020430041054511829 (2 : ZMod 1111020430041054511829)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (25609, 1), (10845995841706573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (25609, 1), (10845995841706573, 1)] : List FactorBlock).map factorBlockValue).prod) = 1111020430041054511829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_25609
      · exact prime_oneHundredFortyTwoEJ_10845995841706573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1111020430041054511829) ^ 555510215020527255914 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1111020430041054511829) ^ 43383983366826292 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1111020430041054511829) ^ 102436 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1360085518360669771409 : Nat.Prime 1360085518360669771409 := by
  apply lucas_primality 1360085518360669771409 (3 : ZMod 1360085518360669771409)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (69931, 1), (63976856057017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (69931, 1), (63976856057017, 1)] : List FactorBlock).map factorBlockValue).prod) = 1360085518360669771409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_69931
      · exact prime_oneHundredFortyTwoEJ_63976856057017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1360085518360669771409) ^ 680042759180334885704 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1360085518360669771409) ^ 71583448334772093232 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1360085518360669771409) ^ 19448964241333168 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1360085518360669771409) ^ 21259024 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1491267086066144291221 : Nat.Prime 1491267086066144291221 := by
  apply lucas_primality 1491267086066144291221 (2 : ZMod 1491267086066144291221)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (53, 1), (2683, 1), (95581, 1), (203185897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (53, 1), (2683, 1), (95581, 1), (203185897, 1)] : List FactorBlock).map factorBlockValue).prod) = 1491267086066144291221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_53
      · exact prime_oneHundredFortyTwoEJ_2683
      · exact prime_oneHundredFortyTwoEJ_95581
      · exact prime_oneHundredFortyTwoEJ_203185897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1491267086066144291221) ^ 745633543033072145610 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1491267086066144291221) ^ 497089028688714763740 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1491267086066144291221) ^ 298253417213228858244 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1491267086066144291221) ^ 28137114831436684740 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1491267086066144291221) ^ 555820755149513340 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1491267086066144291221) ^ 15602128938451620 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1491267086066144291221) ^ 7339422214260 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1776621171433917881161 : Nat.Prime 1776621171433917881161 := by
  apply lucas_primality 1776621171433917881161 (19 : ZMod 1776621171433917881161)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (11, 1), (448641709958060071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (11, 1), (448641709958060071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1776621171433917881161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_448641709958060071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1776621171433917881161) ^ 888310585716958940580 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 1776621171433917881161) ^ 592207057144639293720 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 1776621171433917881161) ^ 355324234286783576232 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 1776621171433917881161) ^ 161511015584901625560 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 1776621171433917881161) ^ 3960 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2139356548036610576603 : Nat.Prime 2139356548036610576603 := by
  apply lucas_primality 2139356548036610576603 (2 : ZMod 2139356548036610576603)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (5975856279431873119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (5975856279431873119, 1)] : List FactorBlock).map factorBlockValue).prod) = 2139356548036610576603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_179
      · exact prime_oneHundredFortyTwoEJ_5975856279431873119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2139356548036610576603) ^ 1069678274018305288301 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139356548036610576603) ^ 11951712558863746238 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139356548036610576603) ^ 358 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2522437275855640699889 : Nat.Prime 2522437275855640699889 := by
  apply lucas_primality 2522437275855640699889 (3 : ZMod 2522437275855640699889)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (227, 1), (130293959, 1), (5330282851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (227, 1), (130293959, 1), (5330282851, 1)] : List FactorBlock).map factorBlockValue).prod) = 2522437275855640699889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_227
      · exact prime_oneHundredFortyTwoEJ_130293959
      · exact prime_oneHundredFortyTwoEJ_5330282851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2522437275855640699889) ^ 1261218637927820349944 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2522437275855640699889) ^ 11112058483945553744 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2522437275855640699889) ^ 19359587314832 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2522437275855640699889) ^ 473227659088 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3133295906584059141703 : Nat.Prime 3133295906584059141703 := by
  apply lucas_primality 3133295906584059141703 (3 : ZMod 3133295906584059141703)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23201, 1), (3215477069527031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23201, 1), (3215477069527031, 1)] : List FactorBlock).map factorBlockValue).prod) = 3133295906584059141703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_23201
      · exact prime_oneHundredFortyTwoEJ_3215477069527031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3133295906584059141703) ^ 1566647953292029570851 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3133295906584059141703) ^ 1044431968861353047234 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3133295906584059141703) ^ 447613700940579877386 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3133295906584059141703) ^ 135050036920135302 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3133295906584059141703) ^ 974442 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3154840275004716510073 : Nat.Prime 3154840275004716510073 := by
  apply lucas_primality 3154840275004716510073 (5 : ZMod 3154840275004716510073)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (43, 1), (113, 1), (151, 1), (2806651, 1), (3039727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (43, 1), (113, 1), (151, 1), (2806651, 1), (3039727, 1)] : List FactorBlock).map factorBlockValue).prod) = 3154840275004716510073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_43
      · exact prime_oneHundredFortyTwoEJ_113
      · exact prime_oneHundredFortyTwoEJ_151
      · exact prime_oneHundredFortyTwoEJ_2806651
      · exact prime_oneHundredFortyTwoEJ_3039727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3154840275004716510073) ^ 1577420137502358255036 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3154840275004716510073) ^ 1051613425001572170024 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3154840275004716510073) ^ 450691467857816644296 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3154840275004716510073) ^ 73368378488481779304 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3154840275004716510073) ^ 27918940486767402744 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3154840275004716510073) ^ 20892981953673619272 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3154840275004716510073) ^ 1124058628951272 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3154840275004716510073) ^ 1037869609673736 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_4796307717391326766529 : Nat.Prime 4796307717391326766529 := by
  apply lucas_primality 4796307717391326766529 (3 : ZMod 4796307717391326766529)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (439, 1), (170711407936764193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (439, 1), (170711407936764193, 1)] : List FactorBlock).map factorBlockValue).prod) = 4796307717391326766529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_439
      · exact prime_oneHundredFortyTwoEJ_170711407936764193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4796307717391326766529) ^ 2398153858695663383264 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4796307717391326766529) ^ 10925530107952908352 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4796307717391326766529) ^ 28096 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_6718647856690347139687 : Nat.Prime 6718647856690347139687 := by
  apply lucas_primality 6718647856690347139687 (3 : ZMod 6718647856690347139687)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (631, 1), (2647, 1), (6019289, 1), (111378697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (631, 1), (2647, 1), (6019289, 1), (111378697, 1)] : List FactorBlock).map factorBlockValue).prod) = 6718647856690347139687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_631
      · exact prime_oneHundredFortyTwoEJ_2647
      · exact prime_oneHundredFortyTwoEJ_6019289
      · exact prime_oneHundredFortyTwoEJ_111378697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6718647856690347139687) ^ 3359323928345173569843 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6718647856690347139687) ^ 2239549285563449046562 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6718647856690347139687) ^ 10647619424231928906 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6718647856690347139687) ^ 2538212261688835338 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6718647856690347139687) ^ 1116186289890774 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6718647856690347139687) ^ 60322557523638 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_7289200744030233980639 : Nat.Prime 7289200744030233980639 := by
  apply lucas_primality 7289200744030233980639 (7 : ZMod 7289200744030233980639)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (51577, 1), (541889, 1), (130401774823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (51577, 1), (541889, 1), (130401774823, 1)] : List FactorBlock).map factorBlockValue).prod) = 7289200744030233980639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_51577
      · exact prime_oneHundredFortyTwoEJ_541889
      · exact prime_oneHundredFortyTwoEJ_130401774823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7289200744030233980639) ^ 3644600372015116990319 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 7289200744030233980639) ^ 141326574714121294 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 7289200744030233980639) ^ 13451464680091742 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 7289200744030233980639) ^ 55898017906 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_7973072782323077943011 : Nat.Prime 7973072782323077943011 := by
  apply lucas_primality 7973072782323077943011 (6 : ZMod 7973072782323077943011)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (41, 1), (1217285549, 1), (2282187727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (41, 1), (1217285549, 1), (2282187727, 1)] : List FactorBlock).map factorBlockValue).prod) = 7973072782323077943011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_41
      · exact prime_oneHundredFortyTwoEJ_1217285549
      · exact prime_oneHundredFortyTwoEJ_2282187727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7973072782323077943011) ^ 3986536391161538971505 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 7973072782323077943011) ^ 1594614556464615588602 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 7973072782323077943011) ^ 1139010397474725420430 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 7973072782323077943011) ^ 194465189812757998610 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 7973072782323077943011) ^ 6549878776490 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 7973072782323077943011) ^ 3493609525630 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_8656573883657270617777 : Nat.Prime 8656573883657270617777 := by
  apply lucas_primality 8656573883657270617777 (7 : ZMod 8656573883657270617777)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (37, 2), (347, 1), (397, 1), (30847479137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (37, 2), (347, 1), (397, 1), (30847479137, 1)] : List FactorBlock).map factorBlockValue).prod) = 8656573883657270617777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_37
      · exact prime_oneHundredFortyTwoEJ_347
      · exact prime_oneHundredFortyTwoEJ_397
      · exact prime_oneHundredFortyTwoEJ_30847479137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8656573883657270617777) ^ 4328286941828635308888 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8656573883657270617777) ^ 2885524627885756872592 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8656573883657270617777) ^ 279244318827653890896 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8656573883657270617777) ^ 233961456315061368048 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8656573883657270617777) ^ 24946898800165045008 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8656573883657270617777) ^ 21804971999136701808 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 8656573883657270617777) ^ 280625001648 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_10326471478956348312757 : Nat.Prime 10326471478956348312757 := by
  apply lucas_primality 10326471478956348312757 (2 : ZMod 10326471478956348312757)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (229, 1), (3757813493069995747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (229, 1), (3757813493069995747, 1)] : List FactorBlock).map factorBlockValue).prod) = 10326471478956348312757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_229
      · exact prime_oneHundredFortyTwoEJ_3757813493069995747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10326471478956348312757) ^ 5163235739478174156378 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10326471478956348312757) ^ 3442157159652116104252 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10326471478956348312757) ^ 45093761916839948964 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10326471478956348312757) ^ 2748 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_17466165153958717009459 : Nat.Prime 17466165153958717009459 := by
  apply lucas_primality 17466165153958717009459 (7 : ZMod 17466165153958717009459)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1031, 1), (104574039072449839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1031, 1), (104574039072449839, 1)] : List FactorBlock).map factorBlockValue).prod) = 17466165153958717009459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_1031
      · exact prime_oneHundredFortyTwoEJ_104574039072449839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 17466165153958717009459) ^ 8733082576979358504729 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 17466165153958717009459) ^ 5822055051319572336486 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 17466165153958717009459) ^ 16940994329736873918 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (7 : ZMod 17466165153958717009459) ^ 167022 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_22583350837779412969543 : Nat.Prime 22583350837779412969543 := by
  apply lucas_primality 22583350837779412969543 (13 : ZMod 22583350837779412969543)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4129, 1), (6961, 1), (9043, 1), (14481317771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4129, 1), (6961, 1), (9043, 1), (14481317771, 1)] : List FactorBlock).map factorBlockValue).prod) = 22583350837779412969543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_4129
      · exact prime_oneHundredFortyTwoEJ_6961
      · exact prime_oneHundredFortyTwoEJ_9043
      · exact prime_oneHundredFortyTwoEJ_14481317771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 22583350837779412969543) ^ 11291675418889706484771 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 22583350837779412969543) ^ 7527783612593137656514 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 22583350837779412969543) ^ 5469448011087288198 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 22583350837779412969543) ^ 3244268185286512422 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 22583350837779412969543) ^ 2497329518719386594 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 22583350837779412969543) ^ 1559481754002 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_26647184275005862489927 : Nat.Prime 26647184275005862489927 := by
  apply lucas_primality 26647184275005862489927 (6 : ZMod 26647184275005862489927)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2467277, 1), (31904701, 1), (56419273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2467277, 1), (31904701, 1), (56419273, 1)] : List FactorBlock).map factorBlockValue).prod) = 26647184275005862489927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_2467277
      · exact prime_oneHundredFortyTwoEJ_31904701
      · exact prime_oneHundredFortyTwoEJ_56419273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 26647184275005862489927) ^ 13323592137502931244963 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 26647184275005862489927) ^ 8882394758335287496642 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 26647184275005862489927) ^ 10800240214214238 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 26647184275005862489927) ^ 835211847777726 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 26647184275005862489927) ^ 472306409815062 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_40989052995258230729189 : Nat.Prime 40989052995258230729189 := by
  apply lucas_primality 40989052995258230729189 (2 : ZMod 40989052995258230729189)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (3023, 1), (484252315524528977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (3023, 1), (484252315524528977, 1)] : List FactorBlock).map factorBlockValue).prod) = 40989052995258230729189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_3023
      · exact prime_oneHundredFortyTwoEJ_484252315524528977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40989052995258230729189) ^ 20494526497629115364594 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40989052995258230729189) ^ 5855578999322604389884 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40989052995258230729189) ^ 13559064834686811356 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40989052995258230729189) ^ 84644 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_45093964182184428335873 : Nat.Prime 45093964182184428335873 := by
  apply lucas_primality 45093964182184428335873 (3 : ZMod 45093964182184428335873)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (53, 1), (114199, 1), (816917, 1), (35625613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (53, 1), (114199, 1), (816917, 1), (35625613, 1)] : List FactorBlock).map factorBlockValue).prod) = 45093964182184428335873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_53
      · exact prime_oneHundredFortyTwoEJ_114199
      · exact prime_oneHundredFortyTwoEJ_816917
      · exact prime_oneHundredFortyTwoEJ_35625613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45093964182184428335873) ^ 22546982091092214167936 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45093964182184428335873) ^ 850829512871404308224 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45093964182184428335873) ^ 394871795569001728 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45093964182184428335873) ^ 55200178454095616 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 45093964182184428335873) ^ 1265773705625344 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_189494289774219885282769 : Nat.Prime 189494289774219885282769 := by
  apply lucas_primality 189494289774219885282769 (11 : ZMod 189494289774219885282769)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 2), (300260509, 1), (7821480379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 2), (300260509, 1), (7821480379, 1)] : List FactorBlock).map factorBlockValue).prod) = 189494289774219885282769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_41
      · exact prime_oneHundredFortyTwoEJ_300260509
      · exact prime_oneHundredFortyTwoEJ_7821480379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 189494289774219885282769) ^ 94747144887109942641384 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 189494289774219885282769) ^ 63164763258073295094256 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 189494289774219885282769) ^ 4621811945712680128848 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 189494289774219885282769) ^ 631099608820752 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 189494289774219885282769) ^ 24227419950192 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_224728259035077966902369 : Nat.Prime 224728259035077966902369 := by
  apply lucas_primality 224728259035077966902369 (3 : ZMod 224728259035077966902369)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (514464281, 1), (718453857241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (514464281, 1), (718453857241, 1)] : List FactorBlock).map factorBlockValue).prod) = 224728259035077966902369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_514464281
      · exact prime_oneHundredFortyTwoEJ_718453857241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 224728259035077966902369) ^ 112364129517538983451184 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 224728259035077966902369) ^ 11827803107109366679072 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 224728259035077966902369) ^ 436819945202528 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 224728259035077966902369) ^ 312794282848 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_291957346923423425028283 : Nat.Prime 291957346923423425028283 := by
  apply lucas_primality 291957346923423425028283 (2 : ZMod 291957346923423425028283)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (811, 1), (3529379692505299981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (811, 1), (3529379692505299981, 1)] : List FactorBlock).map factorBlockValue).prod) = 291957346923423425028283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_811
      · exact prime_oneHundredFortyTwoEJ_3529379692505299981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 291957346923423425028283) ^ 145978673461711712514141 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 291957346923423425028283) ^ 97319115641141141676094 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 291957346923423425028283) ^ 17173961583730789707546 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 291957346923423425028283) ^ 359996728635540598062 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 291957346923423425028283) ^ 82722 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_452039100731851284119609 : Nat.Prime 452039100731851284119609 := by
  apply lucas_primality 452039100731851284119609 (3 : ZMod 452039100731851284119609)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (2347, 1), (20389, 1), (168685968830471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (2347, 1), (20389, 1), (168685968830471, 1)] : List FactorBlock).map factorBlockValue).prod) = 452039100731851284119609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_2347
      · exact prime_oneHundredFortyTwoEJ_20389
      · exact prime_oneHundredFortyTwoEJ_168685968830471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 452039100731851284119609) ^ 226019550365925642059804 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 452039100731851284119609) ^ 64577014390264469159944 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 452039100731851284119609) ^ 192602940235130500264 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 452039100731851284119609) ^ 22170734255326464472 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 452039100731851284119609) ^ 2679767048 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_499586056334032010006527 : Nat.Prime 499586056334032010006527 := by
  apply lucas_primality 499586056334032010006527 (3 : ZMod 499586056334032010006527)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (71, 1), (2110404017, 1), (17925588013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (71, 1), (2110404017, 1), (17925588013, 1)] : List FactorBlock).map factorBlockValue).prod) = 499586056334032010006527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_71
      · exact prime_oneHundredFortyTwoEJ_2110404017
      · exact prime_oneHundredFortyTwoEJ_17925588013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 499586056334032010006527) ^ 249793028167016005003263 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 499586056334032010006527) ^ 166528685444677336668842 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 499586056334032010006527) ^ 16115679236581677742146 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 499586056334032010006527) ^ 7036423328648338169106 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 499586056334032010006527) ^ 236725315299678 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 499586056334032010006527) ^ 27869995448502 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_596713978412906565295913 : Nat.Prime 596713978412906565295913 := by
  apply lucas_primality 596713978412906565295913 (3 : ZMod 596713978412906565295913)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (103967, 1), (731729, 1), (16617987697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (103967, 1), (731729, 1), (16617987697, 1)] : List FactorBlock).map factorBlockValue).prod) = 596713978412906565295913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_59
      · exact prime_oneHundredFortyTwoEJ_103967
      · exact prime_oneHundredFortyTwoEJ_731729
      · exact prime_oneHundredFortyTwoEJ_16617987697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 596713978412906565295913) ^ 298356989206453282647956 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 596713978412906565295913) ^ 10113796244286551954168 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 596713978412906565295913) ^ 5739455581221989336 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 596713978412906565295913) ^ 815484938293967528 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 596713978412906565295913) ^ 35907715741096 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_1232993269162302506695261 : Nat.Prime 1232993269162302506695261 := by
  apply lucas_primality 1232993269162302506695261 (11 : ZMod 1232993269162302506695261)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (19, 1), (79, 1), (557, 1), (8193176549514251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (19, 1), (79, 1), (557, 1), (8193176549514251, 1)] : List FactorBlock).map factorBlockValue).prod) = 1232993269162302506695261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_79
      · exact prime_oneHundredFortyTwoEJ_557
      · exact prime_oneHundredFortyTwoEJ_8193176549514251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1232993269162302506695261) ^ 616496634581151253347630 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1232993269162302506695261) ^ 410997756387434168898420 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1232993269162302506695261) ^ 246598653832460501339052 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1232993269162302506695261) ^ 64894382587489605615540 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1232993269162302506695261) ^ 15607509736231677299940 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1232993269162302506695261) ^ 2213632440147760335180 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 1232993269162302506695261) ^ 150490260 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3217854357559625559813949 : Nat.Prime 3217854357559625559813949 := by
  apply lucas_primality 3217854357559625559813949 (2 : ZMod 3217854357559625559813949)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (29, 1), (390432611, 1), (1393131567923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (29, 1), (390432611, 1), (1393131567923, 1)] : List FactorBlock).map factorBlockValue).prod) = 3217854357559625559813949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_29
      · exact prime_oneHundredFortyTwoEJ_390432611
      · exact prime_oneHundredFortyTwoEJ_1393131567923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3217854357559625559813949) ^ 1608927178779812779906974 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3217854357559625559813949) ^ 1072618119186541853271316 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3217854357559625559813949) ^ 189285550444683856459644 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3217854357559625559813949) ^ 110960495088262950338412 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3217854357559625559813949) ^ 8241766355832468 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3217854357559625559813949) ^ 2309799326676 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_3584998559495201364680291 : Nat.Prime 3584998559495201364680291 := by
  apply lucas_primality 3584998559495201364680291 (2 : ZMod 3584998559495201364680291)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (20437117, 1), (2505943726585591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (20437117, 1), (2505943726585591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3584998559495201364680291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_20437117
      · exact prime_oneHundredFortyTwoEJ_2505943726585591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3584998559495201364680291) ^ 1792499279747600682340145 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3584998559495201364680291) ^ 716999711899040272936058 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3584998559495201364680291) ^ 512142651356457337811470 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3584998559495201364680291) ^ 175416060860991370 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3584998559495201364680291) ^ 1430598190 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_4091088252817057820124119 : Nat.Prime 4091088252817057820124119 := by
  apply lucas_primality 4091088252817057820124119 (11 : ZMod 4091088252817057820124119)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (23, 1), (401, 1), (1979, 1), (7208899, 1), (317267677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (23, 1), (401, 1), (1979, 1), (7208899, 1), (317267677, 1)] : List FactorBlock).map factorBlockValue).prod) = 4091088252817057820124119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_23
      · exact prime_oneHundredFortyTwoEJ_401
      · exact prime_oneHundredFortyTwoEJ_1979
      · exact prime_oneHundredFortyTwoEJ_7208899
      · exact prime_oneHundredFortyTwoEJ_317267677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4091088252817057820124119) ^ 2045544126408528910062059 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 4091088252817057820124119) ^ 584441178973865402874874 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 4091088252817057820124119) ^ 177873402296393818266266 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 4091088252817057820124119) ^ 10202215094306877356918 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 4091088252817057820124119) ^ 2067250254076330379042 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 4091088252817057820124119) ^ 567505281016845682 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (11 : ZMod 4091088252817057820124119) ^ 12894752757360334 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_8008104252175194843856771 : Nat.Prime 8008104252175194843856771 := by
  apply lucas_primality 8008104252175194843856771 (3 : ZMod 8008104252175194843856771)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (179, 1), (1491267086066144291221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (179, 1), (1491267086066144291221, 1)] : List FactorBlock).map factorBlockValue).prod) = 8008104252175194843856771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_179
      · exact prime_oneHundredFortyTwoEJ_1491267086066144291221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8008104252175194843856771) ^ 4004052126087597421928385 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8008104252175194843856771) ^ 2669368084058398281285590 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8008104252175194843856771) ^ 1601620850435038968771354 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8008104252175194843856771) ^ 44738012581984328736630 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8008104252175194843856771) ^ 5370 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_18880105436639764361967313 : Nat.Prime 18880105436639764361967313 := by
  apply lucas_primality 18880105436639764361967313 (19 : ZMod 18880105436639764361967313)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (13, 1), (17, 1), (1833246083, 1), (107871726337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (13, 1), (17, 1), (1833246083, 1), (107871726337, 1)] : List FactorBlock).map factorBlockValue).prod) = 18880105436639764361967313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_1833246083
      · exact prime_oneHundredFortyTwoEJ_107871726337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 18880105436639764361967313) ^ 9440052718319882180983656 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 18880105436639764361967313) ^ 6293368478879921453989104 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 18880105436639764361967313) ^ 1452315802818443412459024 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 18880105436639764361967313) ^ 1110594437449397903645136 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 18880105436639764361967313) ^ 10298729456846064 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 18880105436639764361967313) ^ 175023670036176 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_20966891163057422843338747 : Nat.Prime 20966891163057422843338747 := by
  apply lucas_primality 20966891163057422843338747 (3 : ZMod 20966891163057422843338747)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (8887, 1), (131070922340106165331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (8887, 1), (131070922340106165331, 1)] : List FactorBlock).map factorBlockValue).prod) = 20966891163057422843338747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_8887
      · exact prime_oneHundredFortyTwoEJ_131070922340106165331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20966891163057422843338747) ^ 10483445581528711421669373 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 20966891163057422843338747) ^ 6988963721019140947779582 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 20966891163057422843338747) ^ 2359276602121910975958 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 20966891163057422843338747) ^ 159966 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_27422720931493104329731027 : Nat.Prime 27422720931493104329731027 := by
  apply lucas_primality 27422720931493104329731027 (2 : ZMod 27422720931493104329731027)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (149, 1), (6311, 1), (156788119500149519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (149, 1), (6311, 1), (156788119500149519, 1)] : List FactorBlock).map factorBlockValue).prod) = 27422720931493104329731027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_31
      · exact prime_oneHundredFortyTwoEJ_149
      · exact prime_oneHundredFortyTwoEJ_6311
      · exact prime_oneHundredFortyTwoEJ_156788119500149519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27422720931493104329731027) ^ 13711360465746552164865513 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27422720931493104329731027) ^ 9140906977164368109910342 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27422720931493104329731027) ^ 884603901015906591281646 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27422720931493104329731027) ^ 184045106922772512280074 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27422720931493104329731027) ^ 4345225943827143769566 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27422720931493104329731027) ^ 174903054 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_29850977514687195004732103 : Nat.Prime 29850977514687195004732103 := by
  apply lucas_primality 29850977514687195004732103 (5 : ZMod 29850977514687195004732103)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (367, 1), (1093, 1), (907524751651510081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (367, 1), (1093, 1), (907524751651510081, 1)] : List FactorBlock).map factorBlockValue).prod) = 29850977514687195004732103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_41
      · exact prime_oneHundredFortyTwoEJ_367
      · exact prime_oneHundredFortyTwoEJ_1093
      · exact prime_oneHundredFortyTwoEJ_907524751651510081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 29850977514687195004732103) ^ 14925488757343597502366051 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 29850977514687195004732103) ^ 728072622309443780603222 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 29850977514687195004732103) ^ 81337813391518242519706 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 29850977514687195004732103) ^ 27311049876200544377614 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 29850977514687195004732103) ^ 32892742 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_48450764081558668024996637 : Nat.Prime 48450764081558668024996637 := by
  apply lucas_primality 48450764081558668024996637 (5 : ZMod 48450764081558668024996637)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (6571, 1), (150359813, 1), (1114511899603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (6571, 1), (150359813, 1), (1114511899603, 1)] : List FactorBlock).map factorBlockValue).prod) = 48450764081558668024996637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_6571
      · exact prime_oneHundredFortyTwoEJ_150359813
      · exact prime_oneHundredFortyTwoEJ_1114511899603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 48450764081558668024996637) ^ 24225382040779334012498318 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 48450764081558668024996637) ^ 4404614916505333456817876 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 48450764081558668024996637) ^ 7373423235665601586516 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 48450764081558668024996637) ^ 322232138460817772 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (5 : ZMod 48450764081558668024996637) ^ 43472630573812 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_146878300562205410941918939 : Nat.Prime 146878300562205410941918939 := by
  apply lucas_primality 146878300562205410941918939 (3 : ZMod 146878300562205410941918939)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (499586056334032010006527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (499586056334032010006527, 1)] : List FactorBlock).map factorBlockValue).prod) = 146878300562205410941918939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_7
      · exact prime_oneHundredFortyTwoEJ_499586056334032010006527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 146878300562205410941918939) ^ 73439150281102705470959469 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 146878300562205410941918939) ^ 48959433520735136980639646 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 146878300562205410941918939) ^ 20982614366029344420274134 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 146878300562205410941918939) ^ 294 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_178787963304154190315882159 : Nat.Prime 178787963304154190315882159 := by
  apply lucas_primality 178787963304154190315882159 (19 : ZMod 178787963304154190315882159)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (2383, 1), (16439957, 1), (134225379459077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (2383, 1), (16439957, 1), (134225379459077, 1)] : List FactorBlock).map factorBlockValue).prod) = 178787963304154190315882159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_17
      · exact prime_oneHundredFortyTwoEJ_2383
      · exact prime_oneHundredFortyTwoEJ_16439957
      · exact prime_oneHundredFortyTwoEJ_134225379459077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 178787963304154190315882159) ^ 89393981652077095157941079 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 178787963304154190315882159) ^ 10516939017891422959757774 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 178787963304154190315882159) ^ 75026421864940910749426 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 178787963304154190315882159) ^ 10875208694533336694 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (19 : ZMod 178787963304154190315882159) ^ 1331998196054 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_222066002040477228447901253 : Nat.Prime 222066002040477228447901253 := by
  apply lucas_primality 222066002040477228447901253 (2 : ZMod 222066002040477228447901253)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (19, 1), (406729, 1), (653086426204261433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (19, 1), (406729, 1), (653086426204261433, 1)] : List FactorBlock).map factorBlockValue).prod) = 222066002040477228447901253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_11
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_406729
      · exact prime_oneHundredFortyTwoEJ_653086426204261433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 222066002040477228447901253) ^ 111033001020238614223950626 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 222066002040477228447901253) ^ 20187818367316111677081932 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 222066002040477228447901253) ^ 11687684317919854128836908 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 222066002040477228447901253) ^ 545980252306762557988 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 222066002040477228447901253) ^ 340025444 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_749472756886610646011666729 : Nat.Prime 749472756886610646011666729 := by
  apply lucas_primality 749472756886610646011666729 (3 : ZMod 749472756886610646011666729)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (157, 1), (596713978412906565295913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (157, 1), (596713978412906565295913, 1)] : List FactorBlock).map factorBlockValue).prod) = 749472756886610646011666729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_157
      · exact prime_oneHundredFortyTwoEJ_596713978412906565295913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 749472756886610646011666729) ^ 374736378443305323005833364 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 749472756886610646011666729) ^ 4773711827303252522367304 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 749472756886610646011666729) ^ 1256 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_2798031625710013078443555787 : Nat.Prime 2798031625710013078443555787 := by
  apply lucas_primality 2798031625710013078443555787 (3 : ZMod 2798031625710013078443555787)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (181, 1), (773, 1), (1111020430041054511829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (181, 1), (773, 1), (1111020430041054511829, 1)] : List FactorBlock).map factorBlockValue).prod) = 2798031625710013078443555787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_181
      · exact prime_oneHundredFortyTwoEJ_773
      · exact prime_oneHundredFortyTwoEJ_1111020430041054511829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2798031625710013078443555787) ^ 1399015812855006539221777893 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2798031625710013078443555787) ^ 932677208570004359481185262 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2798031625710013078443555787) ^ 15458738263591232477588706 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2798031625710013078443555787) ^ 3619704561073755599538882 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2798031625710013078443555787) ^ 2518434 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_9875405737800046159212549839 : Nat.Prime 9875405737800046159212549839 := by
  apply lucas_primality 9875405737800046159212549839 (13 : ZMod 9875405737800046159212549839)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (1129, 1), (17519, 1), (1822221349367422937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (1129, 1), (17519, 1), (1822221349367422937, 1)] : List FactorBlock).map factorBlockValue).prod) = 9875405737800046159212549839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_137
      · exact prime_oneHundredFortyTwoEJ_1129
      · exact prime_oneHundredFortyTwoEJ_17519
      · exact prime_oneHundredFortyTwoEJ_1822221349367422937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 9875405737800046159212549839) ^ 4937702868900023079606274919 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 9875405737800046159212549839) ^ 72083253560584278534398174 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 9875405737800046159212549839) ^ 8747037854561599786725022 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 9875405737800046159212549839) ^ 563696885541414815869202 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (13 : ZMod 9875405737800046159212549839) ^ 5419432574 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_11991564110185770336186667661 : Nat.Prime 11991564110185770336186667661 := by
  apply lucas_primality 11991564110185770336186667661 (3 : ZMod 11991564110185770336186667661)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (67, 1), (89, 1), (2139356548036610576603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (67, 1), (89, 1), (2139356548036610576603, 1)] : List FactorBlock).map factorBlockValue).prod) = 11991564110185770336186667661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_47
      · exact prime_oneHundredFortyTwoEJ_67
      · exact prime_oneHundredFortyTwoEJ_89
      · exact prime_oneHundredFortyTwoEJ_2139356548036610576603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11991564110185770336186667661) ^ 5995782055092885168093333830 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11991564110185770336186667661) ^ 2398312822037154067237333532 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11991564110185770336186667661) ^ 255139661918846177365673780 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11991564110185770336186667661) ^ 178978568808742840838606980 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11991564110185770336186667661) ^ 134736675395345734114456940 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11991564110185770336186667661) ^ 5605220 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_18653544171400087189623705251 : Nat.Prime 18653544171400087189623705251 := by
  apply lucas_primality 18653544171400087189623705251 (6 : ZMod 18653544171400087189623705251)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (239, 1), (2351, 1), (11827, 1), (11227840236568807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (239, 1), (2351, 1), (11827, 1), (11227840236568807, 1)] : List FactorBlock).map factorBlockValue).prod) = 18653544171400087189623705251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_5
      · exact prime_oneHundredFortyTwoEJ_239
      · exact prime_oneHundredFortyTwoEJ_2351
      · exact prime_oneHundredFortyTwoEJ_11827
      · exact prime_oneHundredFortyTwoEJ_11227840236568807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 18653544171400087189623705251) ^ 9326772085700043594811852625 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 18653544171400087189623705251) ^ 3730708834280017437924741050 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 18653544171400087189623705251) ^ 78048301972385302048634750 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 18653544171400087189623705251) ^ 7934302072054482003242750 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 18653544171400087189623705251) ^ 1577199980671352599105750 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (6 : ZMod 18653544171400087189623705251) ^ 1661365300750 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyTwoEJ_27980316257100130784435557867 : Nat.Prime 27980316257100130784435557867 := by
  apply lucas_primality 27980316257100130784435557867 (2 : ZMod 27980316257100130784435557867)
  · rw [← oneHundredFortyTwoEJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (18880105436639764361967313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (18880105436639764361967313, 1)] : List FactorBlock).map factorBlockValue).prod) = 27980316257100130784435557867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyTwoEJ_2
      · exact prime_oneHundredFortyTwoEJ_3
      · exact prime_oneHundredFortyTwoEJ_13
      · exact prime_oneHundredFortyTwoEJ_19
      · exact prime_oneHundredFortyTwoEJ_18880105436639764361967313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27980316257100130784435557867) ^ 13990158128550065392217778933 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27980316257100130784435557867) ^ 9326772085700043594811852622 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27980316257100130784435557867) ^ 2152332019776933137264273682 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27980316257100130784435557867) ^ 1472648224057901620233450414 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27980316257100130784435557867) ^ 1482 ≠ 1
      rw [← oneHundredFortyTwoEJFastPow_eq_pow]
      decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347200 : Nat.totient 167881897542600784706613347200 = 66206559136762623864821760000 := by
  rw [← show ((([(2, 7), (5, 2), (71, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_71, prime_oneHundredFortyTwoEJ_171401, prime_oneHundredFortyTwoEJ_714027719, prime_oneHundredFortyTwoEJ_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347201 : Nat.totient 167881897542600784706613347201 = 167881897542011109934592462292 := by
  rw [← show ((([(284702664187, 1), (589674487318220723, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_284702664187, prime_oneHundredFortyTwoEJ_589674487318220723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347202 : Nat.totient 167881897542600784706613347202 = 55960632514200261568871115732 := by
  rw [← show ((([(2, 1), (3, 1), (27980316257100130784435557867, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_27980316257100130784435557867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347203 : Nat.totient 167881897542600784706613347203 = 166106267359898426663548868640 := by
  rw [← show ((([(107, 1), (811, 1), (105863, 1), (18274901311213799053, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_107, prime_oneHundredFortyTwoEJ_811, prime_oneHundredFortyTwoEJ_105863, prime_oneHundredFortyTwoEJ_18274901311213799053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347204 : Nat.totient 167881897542600784706613347204 = 83940948757345162425084165504 := by
  rw [← show ((([(2, 2), (6015017257, 1), (6977614958096236793, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_6015017257, prime_oneHundredFortyTwoEJ_6977614958096236793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347205 : Nat.totient 167881897542600784706613347205 = 69769100277444481955995155840 := by
  rw [← show ((([(3, 2), (5, 1), (7, 1), (11, 1), (48450764081558668024996637, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_11, prime_oneHundredFortyTwoEJ_48450764081558668024996637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347206 : Nat.totient 167881897542600784706613347206 = 83940627006676143399665895264 := by
  rw [← show ((([(2, 1), (260893, 1), (4220329013, 1), (76236884035267, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_260893, prime_oneHundredFortyTwoEJ_4220329013, prime_oneHundredFortyTwoEJ_76236884035267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347207 : Nat.totient 167881897542600784706613347207 = 167881894409304878122500625536 := by
  rw [← show ((([(53579969, 1), (3133295906584059141703, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_53579969, prime_oneHundredFortyTwoEJ_3133295906584059141703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347208 : Nat.totient 167881897542600784706613347208 = 55960352224035196092992451072 := by
  rw [← show ((([(2, 3), (3, 1), (199657, 1), (8880469229, 1), (3945228598639, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_199657, prime_oneHundredFortyTwoEJ_8880469229, prime_oneHundredFortyTwoEJ_3945228598639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347209 : Nat.totient 167881897542600784706613347209 = 154967901917858225103398400000 := by
  rw [← show ((([(13, 1), (44432501, 1), (14778170681, 1), (19667043553, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_13, prime_oneHundredFortyTwoEJ_44432501, prime_oneHundredFortyTwoEJ_14778170681, prime_oneHundredFortyTwoEJ_19667043553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347210 : Nat.totient 167881897542600784706613347210 = 67152727124749184590325144400 := by
  rw [← show ((([(2, 1), (5, 1), (2105611, 1), (7973072782323077943011, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_2105611, prime_oneHundredFortyTwoEJ_7973072782323077943011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347211 : Nat.totient 167881897542600784706613347211 = 107054827450138284278202489024 := by
  rw [← show ((([(3, 1), (23, 1), (362137, 1), (6718647856690347139687, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_23, prime_oneHundredFortyTwoEJ_362137, prime_oneHundredFortyTwoEJ_6718647856690347139687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347212 : Nat.totient 167881897542600784706613347212 = 67711870929212777189409177600 := by
  rw [← show ((([(2, 2), (7, 2), (17, 1), (19891, 1), (40637, 1), (536233, 1), (116243073181, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_17, prime_oneHundredFortyTwoEJ_19891, prime_oneHundredFortyTwoEJ_40637, prime_oneHundredFortyTwoEJ_536233, prime_oneHundredFortyTwoEJ_116243073181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347213 : Nat.totient 167881897542600784706613347213 = 167881897542595748691289981248 := by
  rw [← show ((([(33559898748209, 1), (5002455424617757, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_33559898748209, prime_oneHundredFortyTwoEJ_5002455424617757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347214 : Nat.totient 167881897542600784706613347214 = 55783881122776873177133772288 := by
  rw [← show ((([(2, 1), (3, 4), (359, 1), (2677, 1), (2130133, 1), (506220017507513, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_359, prime_oneHundredFortyTwoEJ_2677, prime_oneHundredFortyTwoEJ_2130133, prime_oneHundredFortyTwoEJ_506220017507513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347215 : Nat.totient 167881897542600784706613347215 = 127081733974252509840399817344 := by
  rw [← show ((([(5, 1), (19, 1), (823, 1), (269683, 1), (1098462487, 1), (7248391259, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_19, prime_oneHundredFortyTwoEJ_823, prime_oneHundredFortyTwoEJ_269683, prime_oneHundredFortyTwoEJ_1098462487, prime_oneHundredFortyTwoEJ_7248391259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347216 : Nat.totient 167881897542600784706613347216 = 76309953426111884066945280000 := by
  rw [← show ((([(2, 4), (11, 1), (32569120651, 1), (29287693336184641, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_11, prime_oneHundredFortyTwoEJ_32569120651, prime_oneHundredFortyTwoEJ_29287693336184641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347217 : Nat.totient 167881897542600784706613347217 = 106475095729452782247366528000 := by
  rw [← show ((([(3, 1), (31, 1), (59, 1), (3831577, 1), (918423551, 1), (8694574633, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_31, prime_oneHundredFortyTwoEJ_59, prime_oneHundredFortyTwoEJ_3831577, prime_oneHundredFortyTwoEJ_918423551, prime_oneHundredFortyTwoEJ_8694574633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347218 : Nat.totient 167881897542600784706613347218 = 83671039023865635410087465200 := by
  rw [← show ((([(2, 1), (311, 1), (26480309, 1), (10192728026288091491, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_311, prime_oneHundredFortyTwoEJ_26480309, prime_oneHundredFortyTwoEJ_10192728026288091491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347219 : Nat.totient 167881897542600784706613347219 = 143778003313278868154342572032 := by
  rw [← show ((([(7, 1), (1997, 1), (2953, 1), (44221633, 1), (91966475174689, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_1997, prime_oneHundredFortyTwoEJ_2953, prime_oneHundredFortyTwoEJ_44221633, prime_oneHundredFortyTwoEJ_91966475174689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347220 : Nat.totient 167881897542600784706613347220 = 44768506011360209255096892576 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (2798031625710013078443555787, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_2798031625710013078443555787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347221 : Nat.totient 167881897542600784706613347221 = 167260069870816031986307250240 := by
  rw [← show ((([(271, 1), (71563, 1), (8656573883657270617777, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_271, prime_oneHundredFortyTwoEJ_71563, prime_oneHundredFortyTwoEJ_8656573883657270617777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347222 : Nat.totient 167881897542600784706613347222 = 77328574483464045482431766400 := by
  rw [← show ((([(2, 1), (13, 1), (613, 1), (2671, 1), (5161411, 1), (764060442704599, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_13, prime_oneHundredFortyTwoEJ_613, prime_oneHundredFortyTwoEJ_2671, prime_oneHundredFortyTwoEJ_5161411, prime_oneHundredFortyTwoEJ_764060442704599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347223 : Nat.totient 167881897542600784706613347223 = 110142216965555393185420001280 := by
  rw [← show ((([(3, 2), (97, 1), (179, 1), (17189, 1), (62500858541336471521, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_97, prime_oneHundredFortyTwoEJ_179, prime_oneHundredFortyTwoEJ_17189, prime_oneHundredFortyTwoEJ_62500858541336471521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347224 : Nat.totient 167881897542600784706613347224 = 81893608557280560480616268800 := by
  rw [← show ((([(2, 3), (41, 1), (957565178891, 1), (534517195034513, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_41, prime_oneHundredFortyTwoEJ_957565178891, prime_oneHundredFortyTwoEJ_534517195034513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347225 : Nat.totient 167881897542600784706613347225 = 132687372895723916081529076800 := by
  rw [← show ((([(5, 2), (83, 1), (20840311, 1), (3882232783126286653, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_83, prime_oneHundredFortyTwoEJ_20840311, prime_oneHundredFortyTwoEJ_3882232783126286653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347226 : Nat.totient 167881897542600784706613347226 = 47962752952580000263646166960 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (13691, 1), (291957346923423425028283, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_13691, prime_oneHundredFortyTwoEJ_291957346923423425028283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347227 : Nat.totient 167881897542600784706613347227 = 147357151448024208081794720800 := by
  rw [← show ((([(11, 1), (29, 1), (5897562454643, 1), (89236111517831, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_11, prime_oneHundredFortyTwoEJ_29, prime_oneHundredFortyTwoEJ_5897562454643, prime_oneHundredFortyTwoEJ_89236111517831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347228 : Nat.totient 167881897542600784706613347228 = 83934513062585273102187019632 := by
  rw [← show ((([(2, 2), (13043, 1), (3217854357559625559813949, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_13043, prime_oneHundredFortyTwoEJ_3217854357559625559813949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347229 : Nat.totient 167881897542600784706613347229 = 104666720685982654833947020032 := by
  rw [← show ((([(3, 1), (17, 1), (157, 1), (20966891163057422843338747, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_17, prime_oneHundredFortyTwoEJ_157, prime_oneHundredFortyTwoEJ_20966891163057422843338747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347230 : Nat.totient 167881897542600784706613347230 = 66831547293277877939045817600 := by
  rw [← show ((([(2, 1), (5, 1), (211, 1), (22639, 1), (3708193927, 1), (947767334281, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_211, prime_oneHundredFortyTwoEJ_22639, prime_oneHundredFortyTwoEJ_3708193927, prime_oneHundredFortyTwoEJ_947767334281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347231 : Nat.totient 167881897542600784706613347231 = 167185208144365410162005606400 := by
  rw [← show ((([(241, 1), (1998947, 1), (443053313, 1), (786555838181, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_241, prime_oneHundredFortyTwoEJ_1998947, prime_oneHundredFortyTwoEJ_443053313, prime_oneHundredFortyTwoEJ_786555838181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347232 : Nat.totient 167881897542600784706613347232 = 53906696811813342505913597952 := by
  rw [← show ((([(2, 5), (3, 2), (43, 1), (73, 2), (14303, 1), (177856633274990129, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_43, prime_oneHundredFortyTwoEJ_73, prime_oneHundredFortyTwoEJ_14303, prime_oneHundredFortyTwoEJ_177856633274990129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347233 : Nat.totient 167881897542600784706613347233 = 143270382727351381218128508096 := by
  rw [← show ((([(7, 1), (229, 1), (18631853, 1), (5621009223087344087, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_229, prime_oneHundredFortyTwoEJ_18631853, prime_oneHundredFortyTwoEJ_5621009223087344087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347234 : Nat.totient 167881897542600784706613347234 = 74750658882438090516991488000 := by
  rw [← show ((([(2, 1), (19, 1), (23, 1), (61, 1), (2153, 1), (2297, 1), (138371, 1), (4601638490971, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_19, prime_oneHundredFortyTwoEJ_23, prime_oneHundredFortyTwoEJ_61, prime_oneHundredFortyTwoEJ_2153, prime_oneHundredFortyTwoEJ_2297, prime_oneHundredFortyTwoEJ_138371, prime_oneHundredFortyTwoEJ_4601638490971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347235 : Nat.totient 167881897542600784706613347235 = 80413098584846248298652770304 := by
  rw [← show ((([(3, 1), (5, 1), (13, 1), (37, 1), (30013, 1), (775279187947180775633, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_13, prime_oneHundredFortyTwoEJ_37, prime_oneHundredFortyTwoEJ_30013, prime_oneHundredFortyTwoEJ_775279187947180775633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347236 : Nat.totient 167881897542600784706613347236 = 83940499314782322197372495360 := by
  rw [← show ((([(2, 2), (186761, 1), (224728259035077966902369, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_186761, prime_oneHundredFortyTwoEJ_224728259035077966902369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347237 : Nat.totient 167881897542600784706613347237 = 167881755147773709386850969600 := by
  rw [← show ((([(1359361, 1), (8885347, 1), (13899355741773911, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_1359361, prime_oneHundredFortyTwoEJ_8885347, prime_oneHundredFortyTwoEJ_13899355741773911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347238 : Nat.totient 167881897542600784706613347238 = 50848642420253355376112522400 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (2063, 1), (1232993269162302506695261, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_11, prime_oneHundredFortyTwoEJ_2063, prime_oneHundredFortyTwoEJ_1232993269162302506695261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347239 : Nat.totient 167881897542600784706613347239 = 167878312544041289505248620120 := by
  rw [← show ((([(46829, 1), (3584998559495201364680291, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_46829, prime_oneHundredFortyTwoEJ_3584998559495201364680291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347240 : Nat.totient 167881897542600784706613347240 = 54870490581681136754841901056 := by
  rw [← show ((([(2, 3), (5, 1), (7, 1), (47, 1), (67, 1), (89, 1), (2139356548036610576603, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_47, prime_oneHundredFortyTwoEJ_67, prime_oneHundredFortyTwoEJ_89, prime_oneHundredFortyTwoEJ_2139356548036610576603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347241 : Nat.totient 167881897542600784706613347241 = 111250619337823534127565249408 := by
  rw [← show ((([(3, 3), (167, 1), (243487, 1), (70990649, 1), (2154005008123, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_167, prime_oneHundredFortyTwoEJ_243487, prime_oneHundredFortyTwoEJ_70990649, prime_oneHundredFortyTwoEJ_2154005008123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347242 : Nat.totient 167881897542600784706613347242 = 83932210662763887000483508224 := by
  rw [← show ((([(2, 1), (9733, 1), (931913, 1), (3544657, 1), (2610823801657, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_9733, prime_oneHundredFortyTwoEJ_931913, prime_oneHundredFortyTwoEJ_3544657, prime_oneHundredFortyTwoEJ_2610823801657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347243 : Nat.totient 167881897542600784706613347243 = 167881708048311010486727178528 := by
  rw [← show ((([(885947, 1), (189494289774219885282769, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_885947, prime_oneHundredFortyTwoEJ_189494289774219885282769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347244 : Nat.totient 167881897542600784706613347244 = 55928600097191560789495681680 := by
  rw [← show ((([(2, 2), (3, 1), (1747, 1), (8008104252175194843856771, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_1747, prime_oneHundredFortyTwoEJ_8008104252175194843856771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347245 : Nat.totient 167881897542600784706613347245 = 132624059799073396261441536000 := by
  rw [← show ((([(5, 1), (151, 1), (257, 1), (487, 1), (1776621171433917881161, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_151, prime_oneHundredFortyTwoEJ_257, prime_oneHundredFortyTwoEJ_487, prime_oneHundredFortyTwoEJ_1776621171433917881161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347246 : Nat.totient 167881897542600784706613347246 = 78352641653688095168365215744 := by
  rw [← show ((([(2, 1), (17, 1), (137, 1), (1129, 1), (17519, 1), (1822221349367422937, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_17, prime_oneHundredFortyTwoEJ_137, prime_oneHundredFortyTwoEJ_1129, prime_oneHundredFortyTwoEJ_17519, prime_oneHundredFortyTwoEJ_1822221349367422937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347247 : Nat.totient 167881897542600784706613347247 = 95932512844384515623016070752 := by
  rw [← show ((([(3, 1), (7, 1), (2585667229, 1), (3091803919620771983, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_2585667229, prime_oneHundredFortyTwoEJ_3091803919620771983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347248 : Nat.totient 167881897542600784706613347248 = 74984438195802633982746792960 := by
  rw [← show ((([(2, 4), (13, 1), (31, 1), (2330837, 1), (11170354011363935573, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_13, prime_oneHundredFortyTwoEJ_31, prime_oneHundredFortyTwoEJ_2330837, prime_oneHundredFortyTwoEJ_11170354011363935573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347249 : Nat.totient 167881897542600784706613347249 = 150762842053703382280100400000 := by
  rw [← show ((([(11, 2), (109, 1), (331, 1), (6030851, 1), (6376544700516061, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_11, prime_oneHundredFortyTwoEJ_109, prime_oneHundredFortyTwoEJ_331, prime_oneHundredFortyTwoEJ_6030851, prime_oneHundredFortyTwoEJ_6376544700516061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347250 : Nat.totient 167881897542600784706613347250 = 44558459598026848784118480000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 3), (239, 1), (2351, 1), (11827, 1), (11227840236568807, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_239, prime_oneHundredFortyTwoEJ_2351, prime_oneHundredFortyTwoEJ_11827, prime_oneHundredFortyTwoEJ_11227840236568807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347251 : Nat.totient 167881897542600784706613347251 = 167881897049623659590841840000 := by
  rw [← show ((([(353649991, 1), (11961811601, 1), (39685628261, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_353649991, prime_oneHundredFortyTwoEJ_11961811601, prime_oneHundredFortyTwoEJ_39685628261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347252 : Nat.totient 167881897542600784706613347252 = 82355262443232575975761889280 := by
  rw [← show ((([(2, 2), (53, 1), (52289, 1), (257519, 1), (58809622940938231, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_53, prime_oneHundredFortyTwoEJ_52289, prime_oneHundredFortyTwoEJ_257519, prime_oneHundredFortyTwoEJ_58809622940938231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347253 : Nat.totient 167881897542600784706613347253 = 106030638357947102118472124832 := by
  rw [← show ((([(3, 1), (19, 2), (3517247, 1), (29223839, 1), (1508117842927, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_19, prime_oneHundredFortyTwoEJ_3517247, prime_oneHundredFortyTwoEJ_29223839, prime_oneHundredFortyTwoEJ_1508117842927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347254 : Nat.totient 167881897542600784706613347254 = 71949384661114622017120005960 := by
  rw [← show ((([(2, 1), (7, 1), (11991564110185770336186667661, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_11991564110185770336186667661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347255 : Nat.totient 167881897542600784706613347255 = 132983182628402251588766588928 := by
  rw [← show ((([(5, 1), (103, 1), (7229, 1), (45093964182184428335873, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_103, prime_oneHundredFortyTwoEJ_7229, prime_oneHundredFortyTwoEJ_45093964182184428335873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347256 : Nat.totient 167881897542600784706613347256 = 53425327153039871268163276800 := by
  rw [← show ((([(2, 3), (3, 1), (29, 1), (101, 1), (757, 1), (3154840275004716510073, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_29, prime_oneHundredFortyTwoEJ_101, prime_oneHundredFortyTwoEJ_757, prime_oneHundredFortyTwoEJ_3154840275004716510073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347257 : Nat.totient 167881897542600784706613347257 = 159161597381532676745008035072 := by
  rw [← show ((([(23, 1), (113, 1), (104714629, 1), (616865144496483667, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_23, prime_oneHundredFortyTwoEJ_113, prime_oneHundredFortyTwoEJ_104714629, prime_oneHundredFortyTwoEJ_616865144496483667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347258 : Nat.totient 167881897542600784706613347258 = 83805171221230014297226282512 := by
  rw [← show ((([(2, 1), (619, 1), (492389, 1), (275406941626342132619, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_619, prime_oneHundredFortyTwoEJ_492389, prime_oneHundredFortyTwoEJ_275406941626342132619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347259 : Nat.totient 167881897542600784706613347259 = 111921265028400523137742231500 := by
  rw [← show ((([(3, 2), (18653544171400087189623705251, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_18653544171400087189623705251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347260 : Nat.totient 167881897542600784706613347260 = 61027210746489670097377747200 := by
  rw [← show ((([(2, 2), (5, 1), (11, 1), (3181, 1), (39107, 1), (6134271843075769199, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_11, prime_oneHundredFortyTwoEJ_3181, prime_oneHundredFortyTwoEJ_39107, prime_oneHundredFortyTwoEJ_6134271843075769199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347261 : Nat.totient 167881897542600784706613347261 = 132829172966913916973643072000 := by
  rw [← show ((([(7, 2), (13, 2), (292241, 1), (23170471, 1), (2993953682371, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_13, prime_oneHundredFortyTwoEJ_292241, prime_oneHundredFortyTwoEJ_23170471, prime_oneHundredFortyTwoEJ_2993953682371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347262 : Nat.totient 167881897542600784706613347262 = 55960632313415917249213551192 := by
  rw [← show ((([(2, 1), (3, 1), (278710139, 1), (100392172159550072143, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_278710139, prime_oneHundredFortyTwoEJ_100392172159550072143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347263 : Nat.totient 167881897542600784706613347263 = 158006491804800738547400797408 := by
  rw [← show ((([(17, 1), (9875405737800046159212549839, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_17, prime_oneHundredFortyTwoEJ_9875405737800046159212549839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347264 : Nat.totient 167881897542600784706613347264 = 83940948018096660954764716800 := by
  rw [← show ((([(2, 6), (111445211, 1), (23537616606092990941, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_111445211, prime_oneHundredFortyTwoEJ_23537616606092990941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347265 : Nat.totient 167881897542600784706613347265 = 87347593288341385415619079680 := by
  rw [← show ((([(3, 1), (5, 1), (41, 1), (15629, 1), (17466165153958717009459, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_41, prime_oneHundredFortyTwoEJ_15629, prime_oneHundredFortyTwoEJ_17466165153958717009459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347266 : Nat.totient 167881897542600784706613347266 = 83813934005828277768354372480 := by
  rw [← show ((([(2, 1), (661, 1), (3503909, 1), (36242620839285681817, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_661, prime_oneHundredFortyTwoEJ_3503909, prime_oneHundredFortyTwoEJ_36242620839285681817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347267 : Nat.totient 167881897542600784706613347267 = 167881887216129305750248777080 := by
  rw [← show ((([(16257431, 1), (10326471478956348312757, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_16257431, prime_oneHundredFortyTwoEJ_10326471478956348312757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347268 : Nat.totient 167881897542600784706613347268 = 47966256440743081344746670432 := by
  rw [← show ((([(2, 2), (3, 3), (7, 1), (222066002040477228447901253, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_222066002040477228447901253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347269 : Nat.totient 167881897542600784706613347269 = 167661290560798312353024153600 := by
  rw [← show ((([(761, 1), (8174106049, 1), (26988512256723821, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_761, prime_oneHundredFortyTwoEJ_8174106049, prime_oneHundredFortyTwoEJ_26988512256723821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347270 : Nat.totient 167881897542600784706613347270 = 67152748927291210460055917184 := by
  rw [← show ((([(2, 1), (5, 1), (6655543, 1), (2522437275855640699889, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_6655543, prime_oneHundredFortyTwoEJ_2522437275855640699889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347271 : Nat.totient 167881897542600784706613347271 = 100094523899390386561426560000 := by
  rw [← show ((([(3, 1), (11, 1), (71, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_11, prime_oneHundredFortyTwoEJ_71, prime_oneHundredFortyTwoEJ_461, prime_oneHundredFortyTwoEJ_69997, prime_oneHundredFortyTwoEJ_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347272 : Nat.totient 167881897542600784706613347272 = 77373733718069209452265608384 := by
  rw [← show ((([(2, 3), (19, 1), (37, 1), (29850977514687195004732103, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_19, prime_oneHundredFortyTwoEJ_37, prime_oneHundredFortyTwoEJ_29850977514687195004732103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347273 : Nat.totient 167881897542600784706613347273 = 167876953377021491703408867328 := by
  rw [← show ((([(34679, 1), (1627649, 1), (2974243683278288063, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_34679, prime_oneHundredFortyTwoEJ_1627649, prime_oneHundredFortyTwoEJ_2974243683278288063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347274 : Nat.totient 167881897542600784706613347274 = 51348185180113408444695859200 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (193, 1), (1427, 1), (12451, 1), (627658986764630603, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_13, prime_oneHundredFortyTwoEJ_193, prime_oneHundredFortyTwoEJ_1427, prime_oneHundredFortyTwoEJ_12451, prime_oneHundredFortyTwoEJ_627658986764630603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347275 : Nat.totient 167881897542600784706613347275 = 112441304056905453569252705280 := by
  rw [← show ((([(5, 2), (7, 1), (43, 1), (214177, 1), (104165651384717728783, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_43, prime_oneHundredFortyTwoEJ_214177, prime_oneHundredFortyTwoEJ_104165651384717728783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347276 : Nat.totient 167881897542600784706613347276 = 81473607929156340826814850432 := by
  rw [← show ((([(2, 2), (59, 1), (79, 1), (1038463, 1), (8671091072656451833, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_59, prime_oneHundredFortyTwoEJ_79, prime_oneHundredFortyTwoEJ_1038463, prime_oneHundredFortyTwoEJ_8671091072656451833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347277 : Nat.totient 167881897542600784706613347277 = 111039995225027290672090717128 := by
  rw [← show ((([(3, 2), (127, 1), (146878300562205410941918939, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_127, prime_oneHundredFortyTwoEJ_146878300562205410941918939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347278 : Nat.totient 167881897542600784706613347278 = 83940941981799964759435029376 := by
  rw [← show ((([(2, 1), (12762437, 1), (395374769, 1), (16635325813163, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_12762437, prime_oneHundredFortyTwoEJ_395374769, prime_oneHundredFortyTwoEJ_16635325813163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347279 : Nat.totient 167881897542600784706613347279 = 162454690242513287566935876000 := by
  rw [← show ((([(31, 1), (13931, 1), (497208349831, 1), (781846452469, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_31, prime_oneHundredFortyTwoEJ_13931, prime_oneHundredFortyTwoEJ_497208349831, prime_oneHundredFortyTwoEJ_781846452469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347280 : Nat.totient 167881897542600784706613347280 = 40195053935749753095439515648 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (17, 1), (23, 1), (373, 1), (4796307717391326766529, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_17, prime_oneHundredFortyTwoEJ_23, prime_oneHundredFortyTwoEJ_373, prime_oneHundredFortyTwoEJ_4796307717391326766529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347281 : Nat.totient 167881897542600784706613347281 = 165791270649119443938137004480 := by
  rw [← show ((([(149, 1), (173, 1), (13268553583, 1), (490849005230191, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_149, prime_oneHundredFortyTwoEJ_173, prime_oneHundredFortyTwoEJ_13268553583, prime_oneHundredFortyTwoEJ_490849005230191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347282 : Nat.totient 167881897542600784706613347282 = 65406693204861012828101836800 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (41257, 1), (329081, 1), (1207757, 1), (66481855457, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_11, prime_oneHundredFortyTwoEJ_41257, prime_oneHundredFortyTwoEJ_329081, prime_oneHundredFortyTwoEJ_1207757, prime_oneHundredFortyTwoEJ_66481855457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347283 : Nat.totient 167881897542600784706613347283 = 111903686678811234050883341280 := by
  rw [← show ((([(3, 1), (6367, 1), (8207857571, 1), (1070823646938373, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_6367, prime_oneHundredFortyTwoEJ_8207857571, prime_oneHundredFortyTwoEJ_1070823646938373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347284 : Nat.totient 167881897542600784706613347284 = 83932766594794758237666404888 := by
  rw [← show ((([(2, 2), (10259, 1), (4091088252817057820124119, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_10259, prime_oneHundredFortyTwoEJ_4091088252817057820124119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347285 : Nat.totient 167881897542600784706613347285 = 129674293270604940000606790656 := by
  rw [← show ((([(5, 1), (29, 1), (35239493909, 1), (32855358051929137, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_29, prime_oneHundredFortyTwoEJ_35239493909, prime_oneHundredFortyTwoEJ_32855358051929137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347286 : Nat.totient 167881897542600784706613347286 = 55524099099800761411603898304 := by
  rw [← show ((([(2, 1), (3, 2), (139, 1), (1637, 1), (40989052995258230729189, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_139, prime_oneHundredFortyTwoEJ_1637, prime_oneHundredFortyTwoEJ_40989052995258230729189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347287 : Nat.totient 167881897542600784706613347287 = 151670715741711635742466189920 := by
  rw [← show ((([(13, 1), (47, 1), (739415447, 1), (371598660635984011, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_13, prime_oneHundredFortyTwoEJ_47, prime_oneHundredFortyTwoEJ_739415447, prime_oneHundredFortyTwoEJ_371598660635984011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347288 : Nat.totient 167881897542600784706613347288 = 83728424834407446851355676320 := by
  rw [← show ((([(2, 3), (419, 1), (6871, 1), (7289200744030233980639, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_419, prime_oneHundredFortyTwoEJ_6871, prime_oneHundredFortyTwoEJ_7289200744030233980639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347289 : Nat.totient 167881897542600784706613347289 = 95927393037529356557324346432 := by
  rw [← show ((([(3, 1), (7, 1), (25339, 1), (71917, 1), (4386958645490472043, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_25339, prime_oneHundredFortyTwoEJ_71917, prime_oneHundredFortyTwoEJ_4386958645490472043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347290 : Nat.totient 167881897542600784706613347290 = 67152753576698240439916879360 := by
  rw [← show ((([(2, 1), (5, 1), (12343481, 1), (1360085518360669771409, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_12343481, prime_oneHundredFortyTwoEJ_1360085518360669771409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347291 : Nat.totient 167881897542600784706613347291 = 159007449918039134192234961408 := by
  rw [← show ((([(19, 1), (4157, 1), (532733, 1), (3989887441480325969, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_19, prime_oneHundredFortyTwoEJ_4157, prime_oneHundredFortyTwoEJ_532733, prime_oneHundredFortyTwoEJ_3989887441480325969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347292 : Nat.totient 167881897542600784706613347292 = 55958824357797334163734513536 := by
  rw [← show ((([(2, 2), (3, 1), (30949, 1), (452039100731851284119609, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_30949, prime_oneHundredFortyTwoEJ_452039100731851284119609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347293 : Nat.totient 167881897542600784706613347293 = 152606377851532545049259832000 := by
  rw [← show ((([(11, 1), (14543, 1), (50651, 1), (7046749, 1), (2940223561559, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_11, prime_oneHundredFortyTwoEJ_14543, prime_oneHundredFortyTwoEJ_50651, prime_oneHundredFortyTwoEJ_7046749, prime_oneHundredFortyTwoEJ_2940223561559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347294 : Nat.totient 167881897542600784706613347294 = 83913526050368899248976939560 := by
  rw [← show ((([(2, 1), (3061, 1), (27422720931493104329731027, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3061, prime_oneHundredFortyTwoEJ_27422720931493104329731027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347295 : Nat.totient 167881897542600784706613347295 = 88069192153273144294275594240 := by
  rw [← show ((([(3, 5), (5, 1), (61, 1), (428136865297, 1), (5290724305189, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_61, prime_oneHundredFortyTwoEJ_428136865297, prime_oneHundredFortyTwoEJ_5290724305189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347296 : Nat.totient 167881897542600784706613347296 = 71949384661114622017120005888 := by
  rw [← show ((([(2, 5), (7, 1), (749472756886610646011666729, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_7, prime_oneHundredFortyTwoEJ_749472756886610646011666729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347297 : Nat.totient 167881897542600784706613347297 = 158006130471187334076786288192 := by
  rw [← show ((([(17, 1), (437287, 1), (22583350837779412969543, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_17, prime_oneHundredFortyTwoEJ_437287, prime_oneHundredFortyTwoEJ_22583350837779412969543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347298 : Nat.totient 167881897542600784706613347298 = 55843971141444285902888119680 := by
  rw [← show ((([(2, 1), (3, 1), (709, 1), (1481, 1), (26647184275005862489927, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_709, prime_oneHundredFortyTwoEJ_1481, prime_oneHundredFortyTwoEJ_26647184275005862489927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347299 : Nat.totient 167881897542600784706613347299 = 166493944037405254114196820000 := by
  rw [← show ((([(131, 1), (1567, 1), (1783799, 1), (192772751, 1), (2378329463, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_131, prime_oneHundredFortyTwoEJ_1567, prime_oneHundredFortyTwoEJ_1783799, prime_oneHundredFortyTwoEJ_192772751, prime_oneHundredFortyTwoEJ_2378329463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347300 : Nat.totient 167881897542600784706613347300 = 61987161908487421937858002560 := by
  rw [← show ((([(2, 2), (5, 2), (13, 1), (237418427, 1), (543933858961233823, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_2, prime_oneHundredFortyTwoEJ_5, prime_oneHundredFortyTwoEJ_13, prime_oneHundredFortyTwoEJ_237418427, prime_oneHundredFortyTwoEJ_543933858961233823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyTwoEJ_167881897542600784706613347301 : Nat.totient 167881897542600784706613347301 = 111563689101792214757110466592 := by
  rw [← show ((([(3, 1), (313, 1), (178787963304154190315882159, 1)] : List FactorBlock).map factorBlockValue).prod) = 167881897542600784706613347301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyTwoEJ_3, prime_oneHundredFortyTwoEJ_313, prime_oneHundredFortyTwoEJ_178787963304154190315882159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFortyTwoEJ : certifiedKill 1 167881897542600784706613347199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347200, phi_oneHundredFortyTwoEJ_167881897542600784706613347201, phi_oneHundredFortyTwoEJ_167881897542600784706613347202,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347203, phi_oneHundredFortyTwoEJ_167881897542600784706613347204, phi_oneHundredFortyTwoEJ_167881897542600784706613347205,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347206, phi_oneHundredFortyTwoEJ_167881897542600784706613347207, phi_oneHundredFortyTwoEJ_167881897542600784706613347208,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347209, phi_oneHundredFortyTwoEJ_167881897542600784706613347210, phi_oneHundredFortyTwoEJ_167881897542600784706613347211,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347212, phi_oneHundredFortyTwoEJ_167881897542600784706613347213, phi_oneHundredFortyTwoEJ_167881897542600784706613347214,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347215, phi_oneHundredFortyTwoEJ_167881897542600784706613347216, phi_oneHundredFortyTwoEJ_167881897542600784706613347217,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347218, phi_oneHundredFortyTwoEJ_167881897542600784706613347219, phi_oneHundredFortyTwoEJ_167881897542600784706613347220,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347221, phi_oneHundredFortyTwoEJ_167881897542600784706613347222, phi_oneHundredFortyTwoEJ_167881897542600784706613347223,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347224, phi_oneHundredFortyTwoEJ_167881897542600784706613347225, phi_oneHundredFortyTwoEJ_167881897542600784706613347226,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347227, phi_oneHundredFortyTwoEJ_167881897542600784706613347228, phi_oneHundredFortyTwoEJ_167881897542600784706613347229,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347230, phi_oneHundredFortyTwoEJ_167881897542600784706613347231, phi_oneHundredFortyTwoEJ_167881897542600784706613347232,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347233, phi_oneHundredFortyTwoEJ_167881897542600784706613347234, phi_oneHundredFortyTwoEJ_167881897542600784706613347235,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347236, phi_oneHundredFortyTwoEJ_167881897542600784706613347237, phi_oneHundredFortyTwoEJ_167881897542600784706613347238,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347239, phi_oneHundredFortyTwoEJ_167881897542600784706613347240, phi_oneHundredFortyTwoEJ_167881897542600784706613347241,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347242, phi_oneHundredFortyTwoEJ_167881897542600784706613347243, phi_oneHundredFortyTwoEJ_167881897542600784706613347244,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347245, phi_oneHundredFortyTwoEJ_167881897542600784706613347246, phi_oneHundredFortyTwoEJ_167881897542600784706613347247,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347248, phi_oneHundredFortyTwoEJ_167881897542600784706613347249, phi_oneHundredFortyTwoEJ_167881897542600784706613347250,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347251, phi_oneHundredFortyTwoEJ_167881897542600784706613347252, phi_oneHundredFortyTwoEJ_167881897542600784706613347253,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347254, phi_oneHundredFortyTwoEJ_167881897542600784706613347255, phi_oneHundredFortyTwoEJ_167881897542600784706613347256,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347257, phi_oneHundredFortyTwoEJ_167881897542600784706613347258, phi_oneHundredFortyTwoEJ_167881897542600784706613347259,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347260, phi_oneHundredFortyTwoEJ_167881897542600784706613347261, phi_oneHundredFortyTwoEJ_167881897542600784706613347262,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347263, phi_oneHundredFortyTwoEJ_167881897542600784706613347264, phi_oneHundredFortyTwoEJ_167881897542600784706613347265,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347266, phi_oneHundredFortyTwoEJ_167881897542600784706613347267, phi_oneHundredFortyTwoEJ_167881897542600784706613347268,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347269, phi_oneHundredFortyTwoEJ_167881897542600784706613347270, phi_oneHundredFortyTwoEJ_167881897542600784706613347271,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347272, phi_oneHundredFortyTwoEJ_167881897542600784706613347273, phi_oneHundredFortyTwoEJ_167881897542600784706613347274,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347275, phi_oneHundredFortyTwoEJ_167881897542600784706613347276, phi_oneHundredFortyTwoEJ_167881897542600784706613347277,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347278, phi_oneHundredFortyTwoEJ_167881897542600784706613347279, phi_oneHundredFortyTwoEJ_167881897542600784706613347280,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347281, phi_oneHundredFortyTwoEJ_167881897542600784706613347282, phi_oneHundredFortyTwoEJ_167881897542600784706613347283,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347284, phi_oneHundredFortyTwoEJ_167881897542600784706613347285, phi_oneHundredFortyTwoEJ_167881897542600784706613347286,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347287, phi_oneHundredFortyTwoEJ_167881897542600784706613347288, phi_oneHundredFortyTwoEJ_167881897542600784706613347289,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347290, phi_oneHundredFortyTwoEJ_167881897542600784706613347291, phi_oneHundredFortyTwoEJ_167881897542600784706613347292,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347293, phi_oneHundredFortyTwoEJ_167881897542600784706613347294, phi_oneHundredFortyTwoEJ_167881897542600784706613347295,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347296, phi_oneHundredFortyTwoEJ_167881897542600784706613347297, phi_oneHundredFortyTwoEJ_167881897542600784706613347298,
    phi_oneHundredFortyTwoEJ_167881897542600784706613347299, phi_oneHundredFortyTwoEJ_167881897542600784706613347300, phi_oneHundredFortyTwoEJ_167881897542600784706613347301
    ]

end TotientTailPeriodKiller
end Erdos249257
