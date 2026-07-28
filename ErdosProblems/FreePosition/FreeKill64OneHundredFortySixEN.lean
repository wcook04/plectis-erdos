import Erdos249257.DiagonalPincerCertificatesT64
/- Kernel-checked off-diagonal certificate at a freely chosen position. -/
namespace Erdos249257
namespace TotientTailPeriodKiller
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private def oneHundredFortySixENFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFortySixENFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFortySixENFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFortySixENFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFortySixENFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFortySixENFastPow a n * oneHundredFortySixENFastPow a n * a else oneHundredFortySixENFastPow a n * oneHundredFortySixENFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFortySixEN_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFortySixEN_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFortySixEN_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFortySixEN_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFortySixEN_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFortySixEN_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFortySixEN_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFortySixEN_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFortySixEN_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFortySixEN_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFortySixEN_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFortySixEN_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFortySixEN_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFortySixEN_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFortySixEN_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFortySixEN_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFortySixEN_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFortySixEN_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFortySixEN_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFortySixEN_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFortySixEN_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFortySixEN_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFortySixEN_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFortySixEN_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFortySixEN_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFortySixEN_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFortySixEN_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFortySixEN_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFortySixEN_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFortySixEN_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFortySixEN_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFortySixEN_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFortySixEN_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFortySixEN_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFortySixEN_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFortySixEN_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFortySixEN_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFortySixEN_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFortySixEN_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFortySixEN_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFortySixEN_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFortySixEN_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFortySixEN_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFortySixEN_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFortySixEN_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFortySixEN_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredFortySixEN_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFortySixEN_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFortySixEN_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFortySixEN_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFortySixEN_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFortySixEN_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFortySixEN_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFortySixEN_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFortySixEN_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFortySixEN_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFortySixEN_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFortySixEN_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFortySixEN_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredFortySixEN_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFortySixEN_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFortySixEN_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFortySixEN_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFortySixEN_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFortySixEN_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredFortySixEN_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFortySixEN_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredFortySixEN_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredFortySixEN_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFortySixEN_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredFortySixEN_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredFortySixEN_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFortySixEN_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredFortySixEN_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredFortySixEN_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredFortySixEN_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredFortySixEN_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredFortySixEN_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredFortySixEN_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredFortySixEN_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredFortySixEN_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredFortySixEN_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFortySixEN_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredFortySixEN_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredFortySixEN_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredFortySixEN_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredFortySixEN_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredFortySixEN_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredFortySixEN_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredFortySixEN_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredFortySixEN_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredFortySixEN_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredFortySixEN_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredFortySixEN_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredFortySixEN_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredFortySixEN_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredFortySixEN_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredFortySixEN_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredFortySixEN_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredFortySixEN_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredFortySixEN_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredFortySixEN_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredFortySixEN_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredFortySixEN_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredFortySixEN_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredFortySixEN_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredFortySixEN_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredFortySixEN_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredFortySixEN_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredFortySixEN_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredFortySixEN_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredFortySixEN_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredFortySixEN_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredFortySixEN_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_oneHundredFortySixEN_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredFortySixEN_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredFortySixEN_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredFortySixEN_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredFortySixEN_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredFortySixEN_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredFortySixEN_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredFortySixEN_1801 : Nat.Prime 1801 := by norm_num

private theorem prime_oneHundredFortySixEN_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredFortySixEN_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_oneHundredFortySixEN_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredFortySixEN_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_oneHundredFortySixEN_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_oneHundredFortySixEN_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredFortySixEN_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredFortySixEN_2017 : Nat.Prime 2017 := by norm_num

private theorem prime_oneHundredFortySixEN_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_oneHundredFortySixEN_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_oneHundredFortySixEN_2207 : Nat.Prime 2207 := by norm_num

private theorem prime_oneHundredFortySixEN_2221 : Nat.Prime 2221 := by norm_num

private theorem prime_oneHundredFortySixEN_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_oneHundredFortySixEN_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_oneHundredFortySixEN_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_oneHundredFortySixEN_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_oneHundredFortySixEN_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_oneHundredFortySixEN_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_oneHundredFortySixEN_2503 : Nat.Prime 2503 := by norm_num

private theorem prime_oneHundredFortySixEN_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_oneHundredFortySixEN_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_oneHundredFortySixEN_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredFortySixEN_2861 : Nat.Prime 2861 := by norm_num

private theorem prime_oneHundredFortySixEN_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_oneHundredFortySixEN_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredFortySixEN_3259 : Nat.Prime 3259 := by norm_num

private theorem prime_oneHundredFortySixEN_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_oneHundredFortySixEN_3613 : Nat.Prime 3613 := by norm_num

private theorem prime_oneHundredFortySixEN_3697 : Nat.Prime 3697 := by norm_num

private theorem prime_oneHundredFortySixEN_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_oneHundredFortySixEN_3917 : Nat.Prime 3917 := by norm_num

private theorem prime_oneHundredFortySixEN_3923 : Nat.Prime 3923 := by norm_num

private theorem prime_oneHundredFortySixEN_4013 : Nat.Prime 4013 := by norm_num

private theorem prime_oneHundredFortySixEN_4019 : Nat.Prime 4019 := by norm_num

private theorem prime_oneHundredFortySixEN_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_oneHundredFortySixEN_4127 : Nat.Prime 4127 := by norm_num

private theorem prime_oneHundredFortySixEN_4217 : Nat.Prime 4217 := by norm_num

private theorem prime_oneHundredFortySixEN_4391 : Nat.Prime 4391 := by norm_num

private theorem prime_oneHundredFortySixEN_4409 : Nat.Prime 4409 := by norm_num

private theorem prime_oneHundredFortySixEN_4519 : Nat.Prime 4519 := by norm_num

private theorem prime_oneHundredFortySixEN_4933 : Nat.Prime 4933 := by norm_num

private theorem prime_oneHundredFortySixEN_4937 : Nat.Prime 4937 := by norm_num

private theorem prime_oneHundredFortySixEN_4957 : Nat.Prime 4957 := by norm_num

private theorem prime_oneHundredFortySixEN_5021 : Nat.Prime 5021 := by norm_num

private theorem prime_oneHundredFortySixEN_5119 : Nat.Prime 5119 := by norm_num

private theorem prime_oneHundredFortySixEN_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_oneHundredFortySixEN_5309 : Nat.Prime 5309 := by norm_num

private theorem prime_oneHundredFortySixEN_5437 : Nat.Prime 5437 := by norm_num

private theorem prime_oneHundredFortySixEN_5641 : Nat.Prime 5641 := by norm_num

private theorem prime_oneHundredFortySixEN_5689 : Nat.Prime 5689 := by norm_num

private theorem prime_oneHundredFortySixEN_5821 : Nat.Prime 5821 := by norm_num

private theorem prime_oneHundredFortySixEN_5839 : Nat.Prime 5839 := by norm_num

private theorem prime_oneHundredFortySixEN_5867 : Nat.Prime 5867 := by norm_num

private theorem prime_oneHundredFortySixEN_5939 : Nat.Prime 5939 := by norm_num

private theorem prime_oneHundredFortySixEN_6079 : Nat.Prime 6079 := by norm_num

private theorem prime_oneHundredFortySixEN_6131 : Nat.Prime 6131 := by norm_num

private theorem prime_oneHundredFortySixEN_6361 : Nat.Prime 6361 := by norm_num

private theorem prime_oneHundredFortySixEN_6581 : Nat.Prime 6581 := by norm_num

private theorem prime_oneHundredFortySixEN_6661 : Nat.Prime 6661 := by norm_num

private theorem prime_oneHundredFortySixEN_6977 : Nat.Prime 6977 := by norm_num

private theorem prime_oneHundredFortySixEN_7451 : Nat.Prime 7451 := by norm_num

private theorem prime_oneHundredFortySixEN_7639 : Nat.Prime 7639 := by norm_num

private theorem prime_oneHundredFortySixEN_7691 : Nat.Prime 7691 := by norm_num

private theorem prime_oneHundredFortySixEN_7933 : Nat.Prime 7933 := by norm_num

private theorem prime_oneHundredFortySixEN_8117 : Nat.Prime 8117 := by norm_num

private theorem prime_oneHundredFortySixEN_8237 : Nat.Prime 8237 := by norm_num

private theorem prime_oneHundredFortySixEN_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredFortySixEN_8293 : Nat.Prime 8293 := by norm_num

private theorem prime_oneHundredFortySixEN_8893 : Nat.Prime 8893 := by norm_num

private theorem prime_oneHundredFortySixEN_9613 : Nat.Prime 9613 := by norm_num

private theorem prime_oneHundredFortySixEN_10133 : Nat.Prime 10133 := by norm_num

private theorem prime_oneHundredFortySixEN_10457 : Nat.Prime 10457 := by norm_num

private theorem prime_oneHundredFortySixEN_10499 : Nat.Prime 10499 := by norm_num

private theorem prime_oneHundredFortySixEN_10613 : Nat.Prime 10613 := by norm_num

private theorem prime_oneHundredFortySixEN_11273 : Nat.Prime 11273 := by norm_num

private theorem prime_oneHundredFortySixEN_11411 : Nat.Prime 11411 := by norm_num

private theorem prime_oneHundredFortySixEN_11939 : Nat.Prime 11939 := by norm_num

private theorem prime_oneHundredFortySixEN_13267 : Nat.Prime 13267 := by norm_num

private theorem prime_oneHundredFortySixEN_13421 : Nat.Prime 13421 := by norm_num

private theorem prime_oneHundredFortySixEN_13807 : Nat.Prime 13807 := by norm_num

private theorem prime_oneHundredFortySixEN_13913 : Nat.Prime 13913 := by norm_num

private theorem prime_oneHundredFortySixEN_13921 : Nat.Prime 13921 := by norm_num

private theorem prime_oneHundredFortySixEN_14197 : Nat.Prime 14197 := by norm_num

private theorem prime_oneHundredFortySixEN_14321 : Nat.Prime 14321 := by norm_num

private theorem prime_oneHundredFortySixEN_14327 : Nat.Prime 14327 := by norm_num

private theorem prime_oneHundredFortySixEN_15061 : Nat.Prime 15061 := by norm_num

private theorem prime_oneHundredFortySixEN_15497 : Nat.Prime 15497 := by norm_num

private theorem prime_oneHundredFortySixEN_15767 : Nat.Prime 15767 := by norm_num

private theorem prime_oneHundredFortySixEN_15919 : Nat.Prime 15919 := by norm_num

private theorem prime_oneHundredFortySixEN_16411 : Nat.Prime 16411 := by norm_num

private theorem prime_oneHundredFortySixEN_16453 : Nat.Prime 16453 := by norm_num

private theorem prime_oneHundredFortySixEN_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFortySixEN_17659 : Nat.Prime 17659 := by norm_num

private theorem prime_oneHundredFortySixEN_18743 : Nat.Prime 18743 := by norm_num

private theorem prime_oneHundredFortySixEN_18787 : Nat.Prime 18787 := by norm_num

private theorem prime_oneHundredFortySixEN_19207 : Nat.Prime 19207 := by norm_num

private theorem prime_oneHundredFortySixEN_20611 : Nat.Prime 20611 := by norm_num

private theorem prime_oneHundredFortySixEN_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFortySixEN_21017 : Nat.Prime 21017 := by norm_num

private theorem prime_oneHundredFortySixEN_21407 : Nat.Prime 21407 := by norm_num

private theorem prime_oneHundredFortySixEN_21929 : Nat.Prime 21929 := by norm_num

private theorem prime_oneHundredFortySixEN_23209 : Nat.Prime 23209 := by norm_num

private theorem prime_oneHundredFortySixEN_23833 : Nat.Prime 23833 := by norm_num

private theorem prime_oneHundredFortySixEN_23911 : Nat.Prime 23911 := by norm_num

private theorem prime_oneHundredFortySixEN_24251 : Nat.Prime 24251 := by norm_num

private theorem prime_oneHundredFortySixEN_24691 : Nat.Prime 24691 := by norm_num

private theorem prime_oneHundredFortySixEN_25391 : Nat.Prime 25391 := by norm_num

private theorem prime_oneHundredFortySixEN_28547 : Nat.Prime 28547 := by norm_num

private theorem prime_oneHundredFortySixEN_28697 : Nat.Prime 28697 := by norm_num

private theorem prime_oneHundredFortySixEN_30097 : Nat.Prime 30097 := by norm_num

private theorem prime_oneHundredFortySixEN_30269 : Nat.Prime 30269 := by norm_num

private theorem prime_oneHundredFortySixEN_31139 : Nat.Prime 31139 := by norm_num

private theorem prime_oneHundredFortySixEN_32603 : Nat.Prime 32603 := by norm_num

private theorem prime_oneHundredFortySixEN_33023 : Nat.Prime 33023 := by norm_num

private theorem prime_oneHundredFortySixEN_34511 : Nat.Prime 34511 := by norm_num

private theorem prime_oneHundredFortySixEN_34807 : Nat.Prime 34807 := by norm_num

private theorem prime_oneHundredFortySixEN_35447 : Nat.Prime 35447 := by norm_num

private theorem prime_oneHundredFortySixEN_38891 : Nat.Prime 38891 := by norm_num

private theorem prime_oneHundredFortySixEN_39139 : Nat.Prime 39139 := by norm_num

private theorem prime_oneHundredFortySixEN_40739 : Nat.Prime 40739 := by norm_num

private theorem prime_oneHundredFortySixEN_40801 : Nat.Prime 40801 := by norm_num

private theorem prime_oneHundredFortySixEN_40927 : Nat.Prime 40927 := by norm_num

private theorem prime_oneHundredFortySixEN_41081 : Nat.Prime 41081 := by norm_num

private theorem prime_oneHundredFortySixEN_41849 : Nat.Prime 41849 := by norm_num

private theorem prime_oneHundredFortySixEN_43103 : Nat.Prime 43103 := by norm_num

private theorem prime_oneHundredFortySixEN_45281 : Nat.Prime 45281 := by norm_num

private theorem prime_oneHundredFortySixEN_47317 : Nat.Prime 47317 := by norm_num

private theorem prime_oneHundredFortySixEN_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredFortySixEN_52453 : Nat.Prime 52453 := by norm_num

private theorem prime_oneHundredFortySixEN_52757 : Nat.Prime 52757 := by norm_num

private theorem prime_oneHundredFortySixEN_55079 : Nat.Prime 55079 := by norm_num

private theorem prime_oneHundredFortySixEN_57829 : Nat.Prime 57829 := by norm_num

private theorem prime_oneHundredFortySixEN_58991 : Nat.Prime 58991 := by norm_num

private theorem prime_oneHundredFortySixEN_59359 : Nat.Prime 59359 := by norm_num

private theorem prime_oneHundredFortySixEN_62351 : Nat.Prime 62351 := by norm_num

private theorem prime_oneHundredFortySixEN_67043 : Nat.Prime 67043 := by norm_num

private theorem prime_oneHundredFortySixEN_67993 : Nat.Prime 67993 := by norm_num

private theorem prime_oneHundredFortySixEN_69401 : Nat.Prime 69401 := by norm_num

private theorem prime_oneHundredFortySixEN_69857 : Nat.Prime 69857 := by norm_num

private theorem prime_oneHundredFortySixEN_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredFortySixEN_70079 : Nat.Prime 70079 := by norm_num

private theorem prime_oneHundredFortySixEN_71359 : Nat.Prime 71359 := by norm_num

private theorem prime_oneHundredFortySixEN_71881 : Nat.Prime 71881 := by norm_num

private theorem prime_oneHundredFortySixEN_73783 : Nat.Prime 73783 := by norm_num

private theorem prime_oneHundredFortySixEN_73951 : Nat.Prime 73951 := by norm_num

private theorem prime_oneHundredFortySixEN_74209 : Nat.Prime 74209 := by norm_num

private theorem prime_oneHundredFortySixEN_75557 : Nat.Prime 75557 := by norm_num

private theorem prime_oneHundredFortySixEN_76243 : Nat.Prime 76243 := by norm_num

private theorem prime_oneHundredFortySixEN_80669 : Nat.Prime 80669 := by norm_num

private theorem prime_oneHundredFortySixEN_82217 : Nat.Prime 82217 := by norm_num

private theorem prime_oneHundredFortySixEN_82699 : Nat.Prime 82699 := by norm_num

private theorem prime_oneHundredFortySixEN_87509 : Nat.Prime 87509 := by norm_num

private theorem prime_oneHundredFortySixEN_90947 : Nat.Prime 90947 := by norm_num

private theorem prime_oneHundredFortySixEN_92993 : Nat.Prime 92993 := by norm_num

private theorem prime_oneHundredFortySixEN_95467 : Nat.Prime 95467 := by norm_num

private theorem prime_oneHundredFortySixEN_95483 : Nat.Prime 95483 := by norm_num

private theorem prime_oneHundredFortySixEN_100391 : Nat.Prime 100391 := by norm_num

private theorem prime_oneHundredFortySixEN_101771 : Nat.Prime 101771 := by norm_num

private theorem prime_oneHundredFortySixEN_101863 : Nat.Prime 101863 := by norm_num

private theorem prime_oneHundredFortySixEN_102409 : Nat.Prime 102409 := by norm_num

private theorem prime_oneHundredFortySixEN_110039 : Nat.Prime 110039 := by norm_num

private theorem prime_oneHundredFortySixEN_110681 : Nat.Prime 110681 := by norm_num

private theorem prime_oneHundredFortySixEN_110771 : Nat.Prime 110771 := by norm_num

private theorem prime_oneHundredFortySixEN_127609 : Nat.Prime 127609 := by norm_num

private theorem prime_oneHundredFortySixEN_129001 : Nat.Prime 129001 := by norm_num

private theorem prime_oneHundredFortySixEN_132547 : Nat.Prime 132547 := by norm_num

private theorem prime_oneHundredFortySixEN_136193 : Nat.Prime 136193 := by norm_num

private theorem prime_oneHundredFortySixEN_141221 : Nat.Prime 141221 := by norm_num

private theorem prime_oneHundredFortySixEN_145807 : Nat.Prime 145807 := by norm_num

private theorem prime_oneHundredFortySixEN_150067 : Nat.Prime 150067 := by norm_num

private theorem prime_oneHundredFortySixEN_154589 : Nat.Prime 154589 := by norm_num

private theorem prime_oneHundredFortySixEN_164117 : Nat.Prime 164117 := by norm_num

private theorem prime_oneHundredFortySixEN_166349 : Nat.Prime 166349 := by norm_num

private theorem prime_oneHundredFortySixEN_170609 : Nat.Prime 170609 := by norm_num

private theorem prime_oneHundredFortySixEN_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFortySixEN_174469 : Nat.Prime 174469 := by norm_num

private theorem prime_oneHundredFortySixEN_195197 : Nat.Prime 195197 := by norm_num

private theorem prime_oneHundredFortySixEN_214499 : Nat.Prime 214499 := by norm_num

private theorem prime_oneHundredFortySixEN_216731 : Nat.Prime 216731 := by norm_num

private theorem prime_oneHundredFortySixEN_217333 : Nat.Prime 217333 := by norm_num

private theorem prime_oneHundredFortySixEN_217387 : Nat.Prime 217387 := by norm_num

private theorem prime_oneHundredFortySixEN_233297 : Nat.Prime 233297 := by norm_num

private theorem prime_oneHundredFortySixEN_233407 : Nat.Prime 233407 := by norm_num

private theorem prime_oneHundredFortySixEN_236129 : Nat.Prime 236129 := by norm_num

private theorem prime_oneHundredFortySixEN_241069 : Nat.Prime 241069 := by norm_num

private theorem prime_oneHundredFortySixEN_255803 : Nat.Prime 255803 := by norm_num

private theorem prime_oneHundredFortySixEN_257561 : Nat.Prime 257561 := by norm_num

private theorem prime_oneHundredFortySixEN_261329 : Nat.Prime 261329 := by norm_num

private theorem prime_oneHundredFortySixEN_267551 : Nat.Prime 267551 := by norm_num

private theorem prime_oneHundredFortySixEN_272533 : Nat.Prime 272533 := by norm_num

private theorem prime_oneHundredFortySixEN_275459 : Nat.Prime 275459 := by norm_num

private theorem prime_oneHundredFortySixEN_294059 : Nat.Prime 294059 := by norm_num

private theorem prime_oneHundredFortySixEN_309109 : Nat.Prime 309109 := by norm_num

private theorem prime_oneHundredFortySixEN_319489 : Nat.Prime 319489 := by norm_num

private theorem prime_oneHundredFortySixEN_320839 : Nat.Prime 320839 := by norm_num

private theorem prime_oneHundredFortySixEN_321311 : Nat.Prime 321311 := by norm_num

private theorem prime_oneHundredFortySixEN_333029 : Nat.Prime 333029 := by norm_num

private theorem prime_oneHundredFortySixEN_333457 : Nat.Prime 333457 := by norm_num

private theorem prime_oneHundredFortySixEN_334721 : Nat.Prime 334721 := by norm_num

private theorem prime_oneHundredFortySixEN_348247 : Nat.Prime 348247 := by norm_num

private theorem prime_oneHundredFortySixEN_348617 : Nat.Prime 348617 := by norm_num

private theorem prime_oneHundredFortySixEN_356077 : Nat.Prime 356077 := by norm_num

private theorem prime_oneHundredFortySixEN_375251 : Nat.Prime 375251 := by norm_num

private theorem prime_oneHundredFortySixEN_380753 : Nat.Prime 380753 := by norm_num

private theorem prime_oneHundredFortySixEN_385393 : Nat.Prime 385393 := by norm_num

private theorem prime_oneHundredFortySixEN_389659 : Nat.Prime 389659 := by norm_num

private theorem prime_oneHundredFortySixEN_393727 : Nat.Prime 393727 := by norm_num

private theorem prime_oneHundredFortySixEN_401237 : Nat.Prime 401237 := by norm_num

private theorem prime_oneHundredFortySixEN_417839 : Nat.Prime 417839 := by norm_num

private theorem prime_oneHundredFortySixEN_440131 : Nat.Prime 440131 := by norm_num

private theorem prime_oneHundredFortySixEN_443431 : Nat.Prime 443431 := by norm_num

private theorem prime_oneHundredFortySixEN_461183 : Nat.Prime 461183 := by norm_num

private theorem prime_oneHundredFortySixEN_498469 : Nat.Prime 498469 := by norm_num

private theorem prime_oneHundredFortySixEN_543811 : Nat.Prime 543811 := by norm_num

private theorem prime_oneHundredFortySixEN_617471 : Nat.Prime 617471 := by norm_num

private theorem prime_oneHundredFortySixEN_638171 : Nat.Prime 638171 := by norm_num

private theorem prime_oneHundredFortySixEN_640219 : Nat.Prime 640219 := by norm_num

private theorem prime_oneHundredFortySixEN_677561 : Nat.Prime 677561 := by norm_num

private theorem prime_oneHundredFortySixEN_700423 : Nat.Prime 700423 := by norm_num

private theorem prime_oneHundredFortySixEN_808399 : Nat.Prime 808399 := by norm_num

private theorem prime_oneHundredFortySixEN_830957 : Nat.Prime 830957 := by norm_num

private theorem prime_oneHundredFortySixEN_958459 : Nat.Prime 958459 := by norm_num

private theorem prime_oneHundredFortySixEN_990719 : Nat.Prime 990719 := by norm_num

private theorem prime_oneHundredFortySixEN_1022629 : Nat.Prime 1022629 := by norm_num

private theorem prime_oneHundredFortySixEN_1031281 : Nat.Prime 1031281 := by norm_num

private theorem prime_oneHundredFortySixEN_1055489 : Nat.Prime 1055489 := by norm_num

private theorem prime_oneHundredFortySixEN_1070789 : Nat.Prime 1070789 := by norm_num

private theorem prime_oneHundredFortySixEN_1084661 : Nat.Prime 1084661 := by norm_num

private theorem prime_oneHundredFortySixEN_1159541 : Nat.Prime 1159541 := by norm_num

private theorem prime_oneHundredFortySixEN_1175579 : Nat.Prime 1175579 := by norm_num

private theorem prime_oneHundredFortySixEN_1175743 : Nat.Prime 1175743 := by norm_num

private theorem prime_oneHundredFortySixEN_1218821 : Nat.Prime 1218821 := by norm_num

private theorem prime_oneHundredFortySixEN_1255357 : Nat.Prime 1255357 := by norm_num

private theorem prime_oneHundredFortySixEN_1274209 : Nat.Prime 1274209 := by norm_num

private theorem prime_oneHundredFortySixEN_1300193 : Nat.Prime 1300193 := by norm_num

private theorem prime_oneHundredFortySixEN_1441553 : Nat.Prime 1441553 := by norm_num

private theorem prime_oneHundredFortySixEN_1441771 : Nat.Prime 1441771 := by norm_num

private theorem prime_oneHundredFortySixEN_1493257 : Nat.Prime 1493257 := by norm_num

private theorem prime_oneHundredFortySixEN_1494643 : Nat.Prime 1494643 := by norm_num

private theorem prime_oneHundredFortySixEN_1569643 : Nat.Prime 1569643 := by norm_num

private theorem prime_oneHundredFortySixEN_1616963 : Nat.Prime 1616963 := by norm_num

private theorem prime_oneHundredFortySixEN_1638463 : Nat.Prime 1638463 := by norm_num

private theorem prime_oneHundredFortySixEN_1691423 : Nat.Prime 1691423 := by norm_num

private theorem prime_oneHundredFortySixEN_1756597 : Nat.Prime 1756597 := by norm_num

private theorem prime_oneHundredFortySixEN_1785803 : Nat.Prime 1785803 := by norm_num

private theorem prime_oneHundredFortySixEN_1993661 : Nat.Prime 1993661 := by norm_num

private theorem prime_oneHundredFortySixEN_2111497 : Nat.Prime 2111497 := by norm_num

private theorem prime_oneHundredFortySixEN_2165413 : Nat.Prime 2165413 := by norm_num

private theorem prime_oneHundredFortySixEN_2185373 : Nat.Prime 2185373 := by norm_num

private theorem prime_oneHundredFortySixEN_2722883 : Nat.Prime 2722883 := by norm_num

private theorem prime_oneHundredFortySixEN_2761747 : Nat.Prime 2761747 := by norm_num

private theorem prime_oneHundredFortySixEN_2969059 : Nat.Prime 2969059 := by norm_num

private theorem prime_oneHundredFortySixEN_3017087 : Nat.Prime 3017087 := by norm_num

private theorem prime_oneHundredFortySixEN_3159089 : Nat.Prime 3159089 := by norm_num

private theorem prime_oneHundredFortySixEN_3196847 : Nat.Prime 3196847 := by norm_num

private theorem prime_oneHundredFortySixEN_3423263 : Nat.Prime 3423263 := by norm_num

private theorem prime_oneHundredFortySixEN_3579271 : Nat.Prime 3579271 := by norm_num

private theorem prime_oneHundredFortySixEN_3634723 : Nat.Prime 3634723 := by norm_num

private theorem prime_oneHundredFortySixEN_3658381 : Nat.Prime 3658381 := by norm_num

private theorem prime_oneHundredFortySixEN_3808793 : Nat.Prime 3808793 := by norm_num

private theorem prime_oneHundredFortySixEN_3819821 : Nat.Prime 3819821 := by norm_num

private theorem prime_oneHundredFortySixEN_4033489 : Nat.Prime 4033489 := by norm_num

private theorem prime_oneHundredFortySixEN_4109071 : Nat.Prime 4109071 := by norm_num

private theorem prime_oneHundredFortySixEN_4157501 : Nat.Prime 4157501 := by norm_num

private theorem prime_oneHundredFortySixEN_4161263 : Nat.Prime 4161263 := by norm_num

private theorem prime_oneHundredFortySixEN_4226993 : Nat.Prime 4226993 := by norm_num

private theorem prime_oneHundredFortySixEN_4312699 : Nat.Prime 4312699 := by norm_num

private theorem prime_oneHundredFortySixEN_4459597 : Nat.Prime 4459597 := by norm_num

private theorem prime_oneHundredFortySixEN_4641139 : Nat.Prime 4641139 := by norm_num

private theorem prime_oneHundredFortySixEN_4689809 : Nat.Prime 4689809 := by norm_num

private theorem prime_oneHundredFortySixEN_4766563 : Nat.Prime 4766563 := by norm_num

private theorem prime_oneHundredFortySixEN_4834463 : Nat.Prime 4834463 := by norm_num

private theorem prime_oneHundredFortySixEN_5005709 : Nat.Prime 5005709 := by norm_num

private theorem prime_oneHundredFortySixEN_5371007 : Nat.Prime 5371007 := by norm_num

private theorem prime_oneHundredFortySixEN_5597927 : Nat.Prime 5597927 := by norm_num

private theorem prime_oneHundredFortySixEN_5753323 : Nat.Prime 5753323 := by norm_num

private theorem prime_oneHundredFortySixEN_5801729 : Nat.Prime 5801729 := by norm_num

private theorem prime_oneHundredFortySixEN_5950283 : Nat.Prime 5950283 := by norm_num

private theorem prime_oneHundredFortySixEN_6301853 : Nat.Prime 6301853 := by norm_num

private theorem prime_oneHundredFortySixEN_7019867 : Nat.Prime 7019867 := by norm_num

private theorem prime_oneHundredFortySixEN_7244953 : Nat.Prime 7244953 := by norm_num

private theorem prime_oneHundredFortySixEN_7553603 : Nat.Prime 7553603 := by norm_num

private theorem prime_oneHundredFortySixEN_7595629 : Nat.Prime 7595629 := by norm_num

private theorem prime_oneHundredFortySixEN_7959821 : Nat.Prime 7959821 := by norm_num

private theorem prime_oneHundredFortySixEN_9394201 : Nat.Prime 9394201 := by norm_num

private theorem prime_oneHundredFortySixEN_9737093 : Nat.Prime 9737093 := by norm_num

private theorem prime_oneHundredFortySixEN_10457609 : Nat.Prime 10457609 := by norm_num

private theorem prime_oneHundredFortySixEN_10715909 : Nat.Prime 10715909 := by norm_num

private theorem prime_oneHundredFortySixEN_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFortySixEN_11544359 : Nat.Prime 11544359 := by norm_num

private theorem prime_oneHundredFortySixEN_11946629 : Nat.Prime 11946629 := by norm_num

private theorem prime_oneHundredFortySixEN_12244327 : Nat.Prime 12244327 := by norm_num

private theorem prime_oneHundredFortySixEN_12528469 : Nat.Prime 12528469 := by norm_num

private theorem prime_oneHundredFortySixEN_14548307 : Nat.Prime 14548307 := by norm_num

private theorem prime_oneHundredFortySixEN_15435397 : Nat.Prime 15435397 := by norm_num

private theorem prime_oneHundredFortySixEN_17443301 : Nat.Prime 17443301 := by norm_num

private theorem prime_oneHundredFortySixEN_18743953 : Nat.Prime 18743953 := by norm_num

private theorem prime_oneHundredFortySixEN_19239301 : Nat.Prime 19239301 := by norm_num

private theorem prime_oneHundredFortySixEN_19611029 : Nat.Prime 19611029 := by norm_num

private theorem prime_oneHundredFortySixEN_19941931 : Nat.Prime 19941931 := by norm_num

private theorem prime_oneHundredFortySixEN_20703439 : Nat.Prime 20703439 := by norm_num

private theorem prime_oneHundredFortySixEN_20777101 : Nat.Prime 20777101 := by norm_num

private theorem prime_oneHundredFortySixEN_20873507 : Nat.Prime 20873507 := by norm_num

private theorem prime_oneHundredFortySixEN_22705061 : Nat.Prime 22705061 := by norm_num

private theorem prime_oneHundredFortySixEN_24974129 : Nat.Prime 24974129 := by norm_num

private theorem prime_oneHundredFortySixEN_28495237 : Nat.Prime 28495237 := by norm_num

private theorem prime_oneHundredFortySixEN_28497323 : Nat.Prime 28497323 := by norm_num

private theorem prime_oneHundredFortySixEN_30318083 : Nat.Prime 30318083 := by
  apply lucas_primality 30318083 (2 : ZMod 30318083)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (100391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (100391, 1)] : List FactorBlock).map factorBlockValue).prod) = 30318083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_151
      · exact prime_oneHundredFortySixEN_100391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30318083) ^ 15159041 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 30318083) ^ 200782 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 30318083) ^ 302 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_31602227 : Nat.Prime 31602227 := by
  apply lucas_primality 31602227 (2 : ZMod 31602227)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (385393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (385393, 1)] : List FactorBlock).map factorBlockValue).prod) = 31602227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_41
      · exact prime_oneHundredFortySixEN_385393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31602227) ^ 15801113 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 31602227) ^ 770786 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 31602227) ^ 82 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_31626869 : Nat.Prime 31626869 := by
  apply lucas_primality 31626869 (2 : ZMod 31626869)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (17, 1), (19, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (17, 1), (19, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) = 31626869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_17
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31626869) ^ 15813434 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 31626869) ^ 4518124 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 31626869) ^ 2432836 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 31626869) ^ 1860404 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 31626869) ^ 1664572 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 31626869) ^ 117572 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_31881203 : Nat.Prime 31881203 := by
  apply lucas_primality 31881203 (5 : ZMod 31881203)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (769, 1), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (769, 1), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) = 31881203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_769
      · exact prime_oneHundredFortySixEN_1091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31881203) ^ 15940601 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 31881203) ^ 1677958 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 31881203) ^ 41458 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 31881203) ^ 29222 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_32674597 : Nat.Prime 32674597 := by
  apply lucas_primality 32674597 (2 : ZMod 32674597)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2722883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2722883, 1)] : List FactorBlock).map factorBlockValue).prod) = 32674597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_2722883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32674597) ^ 16337298 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 32674597) ^ 10891532 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 32674597) ^ 12 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_35267371 : Nat.Prime 35267371 := by
  apply lucas_primality 35267371 (2 : ZMod 35267371)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1175579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1175579, 1)] : List FactorBlock).map factorBlockValue).prod) = 35267371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_1175579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35267371) ^ 17633685 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 35267371) ^ 11755790 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 35267371) ^ 7053474 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 35267371) ^ 30 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_38021453 : Nat.Prime 38021453 := by
  apply lucas_primality 38021453 (2 : ZMod 38021453)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (17, 1), (11411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (17, 1), (11411, 1)] : List FactorBlock).map factorBlockValue).prod) = 38021453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_17
      · exact prime_oneHundredFortySixEN_11411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38021453) ^ 19010726 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 38021453) ^ 5431636 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 38021453) ^ 2236556 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 38021453) ^ 3332 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_42080417 : Nat.Prime 42080417 := by
  apply lucas_primality 42080417 (3 : ZMod 42080417)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (47, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (47, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) = 42080417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_47
      · exact prime_oneHundredFortySixEN_571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 42080417) ^ 21040208 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 42080417) ^ 6011488 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 42080417) ^ 895328 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 42080417) ^ 73696 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_47554513 : Nat.Prime 47554513 := by
  apply lucas_primality 47554513 (5 : ZMod 47554513)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (990719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (990719, 1)] : List FactorBlock).map factorBlockValue).prod) = 47554513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_990719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 47554513) ^ 23777256 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 47554513) ^ 15851504 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 47554513) ^ 48 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_47764799 : Nat.Prime 47764799 := by
  apply lucas_primality 47764799 (11 : ZMod 47764799)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (193, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (193, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) = 47764799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_17
      · exact prime_oneHundredFortySixEN_29
      · exact prime_oneHundredFortySixEN_193
      · exact prime_oneHundredFortySixEN_251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 47764799) ^ 23882399 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 47764799) ^ 2809694 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 47764799) ^ 1647062 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 47764799) ^ 247486 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 47764799) ^ 190298 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_48194093 : Nat.Prime 48194093 := by
  apply lucas_primality 48194093 (2 : ZMod 48194093)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3259, 1), (3697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3259, 1), (3697, 1)] : List FactorBlock).map factorBlockValue).prod) = 48194093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3259
      · exact prime_oneHundredFortySixEN_3697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 48194093) ^ 24097046 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 48194093) ^ 14788 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 48194093) ^ 13036 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_48977309 : Nat.Prime 48977309 := by
  apply lucas_primality 48977309 (2 : ZMod 48977309)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (12244327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (12244327, 1)] : List FactorBlock).map factorBlockValue).prod) = 48977309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_12244327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 48977309) ^ 24488654 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 48977309) ^ 4 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_52974709 : Nat.Prime 52974709 := by
  apply lucas_primality 52974709 (2 : ZMod 52974709)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (269, 1), (16411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (269, 1), (16411, 1)] : List FactorBlock).map factorBlockValue).prod) = 52974709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_269
      · exact prime_oneHundredFortySixEN_16411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52974709) ^ 26487354 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 52974709) ^ 17658236 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 52974709) ^ 196932 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 52974709) ^ 3228 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_55283093 : Nat.Prime 55283093 := by
  apply lucas_primality 55283093 (2 : ZMod 55283093)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (294059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (294059, 1)] : List FactorBlock).map factorBlockValue).prod) = 55283093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_47
      · exact prime_oneHundredFortySixEN_294059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55283093) ^ 27641546 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 55283093) ^ 1176236 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 55283093) ^ 188 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_57547577 : Nat.Prime 57547577 := by
  apply lucas_primality 57547577 (3 : ZMod 57547577)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (521, 1), (13807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (521, 1), (13807, 1)] : List FactorBlock).map factorBlockValue).prod) = 57547577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_521
      · exact prime_oneHundredFortySixEN_13807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 57547577) ^ 28773788 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 57547577) ^ 110456 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 57547577) ^ 4168 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_59325377 : Nat.Prime 59325377 := by
  apply lucas_primality 59325377 (3 : ZMod 59325377)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (11, 1), (17, 1), (4957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (11, 1), (17, 1), (4957, 1)] : List FactorBlock).map factorBlockValue).prod) = 59325377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_17
      · exact prime_oneHundredFortySixEN_4957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59325377) ^ 29662688 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 59325377) ^ 5393216 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 59325377) ^ 3489728 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 59325377) ^ 11968 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_1811
      · exact prime_oneHundredFortySixEN_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_63918103 : Nat.Prime 63918103 := by
  apply lucas_primality 63918103 (3 : ZMod 63918103)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2053, 1), (5189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2053, 1), (5189, 1)] : List FactorBlock).map factorBlockValue).prod) = 63918103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_2053
      · exact prime_oneHundredFortySixEN_5189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 63918103) ^ 31959051 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 63918103) ^ 21306034 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 63918103) ^ 31134 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 63918103) ^ 12318 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_68295683 : Nat.Prime 68295683 := by
  apply lucas_primality 68295683 (2 : ZMod 68295683)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (375251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (375251, 1)] : List FactorBlock).map factorBlockValue).prod) = 68295683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_375251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68295683) ^ 34147841 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 68295683) ^ 9756526 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 68295683) ^ 5253514 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 68295683) ^ 182 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_68465261 : Nat.Prime 68465261 := by
  apply lucas_primality 68465261 (3 : ZMod 68465261)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3423263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3423263, 1)] : List FactorBlock).map factorBlockValue).prod) = 68465261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_3423263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68465261) ^ 34232630 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 68465261) ^ 13693052 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 68465261) ^ 20 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_90676081 : Nat.Prime 90676081 := by
  apply lucas_primality 90676081 (14 : ZMod 90676081)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (11, 1), (107, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (11, 1), (107, 2)] : List FactorBlock).map factorBlockValue).prod) = 90676081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 90676081) ^ 45338040 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (14 : ZMod 90676081) ^ 30225360 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (14 : ZMod 90676081) ^ 18135216 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (14 : ZMod 90676081) ^ 8243280 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (14 : ZMod 90676081) ^ 847440 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_91147549 : Nat.Prime 91147549 := by
  apply lucas_primality 91147549 (2 : ZMod 91147549)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7595629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7595629, 1)] : List FactorBlock).map factorBlockValue).prod) = 91147549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7595629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 91147549) ^ 45573774 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 91147549) ^ 30382516 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 91147549) ^ 12 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_94697401 : Nat.Prime 94697401 := by
  apply lucas_primality 94697401 (11 : ZMod 94697401)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (7, 2), (3221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (7, 2), (3221, 1)] : List FactorBlock).map factorBlockValue).prod) = 94697401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_3221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 94697401) ^ 47348700 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 94697401) ^ 31565800 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 94697401) ^ 18939480 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 94697401) ^ 13528200 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 94697401) ^ 29400 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_105045767 : Nat.Prime 105045767 := by
  apply lucas_primality 105045767 (7 : ZMod 105045767)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1289, 1), (5821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1289, 1), (5821, 1)] : List FactorBlock).map factorBlockValue).prod) = 105045767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_1289
      · exact prime_oneHundredFortySixEN_5821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 105045767) ^ 52522883 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 105045767) ^ 15006538 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 105045767) ^ 81494 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 105045767) ^ 18046 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_108175621 : Nat.Prime 108175621 := by
  apply lucas_primality 108175621 (10 : ZMod 108175621)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (257561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (257561, 1)] : List FactorBlock).map factorBlockValue).prod) = 108175621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_257561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 108175621) ^ 54087810 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 108175621) ^ 36058540 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 108175621) ^ 21635124 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 108175621) ^ 15453660 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 108175621) ^ 420 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_117276293 : Nat.Prime 117276293 := by
  apply lucas_primality 117276293 (2 : ZMod 117276293)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (191, 1), (21929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (191, 1), (21929, 1)] : List FactorBlock).map factorBlockValue).prod) = 117276293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_191
      · exact prime_oneHundredFortySixEN_21929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 117276293) ^ 58638146 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 117276293) ^ 16753756 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 117276293) ^ 614012 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 117276293) ^ 5348 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_138410017 : Nat.Prime 138410017 := by
  apply lucas_primality 138410017 (5 : ZMod 138410017)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1441771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1441771, 1)] : List FactorBlock).map factorBlockValue).prod) = 138410017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_1441771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 138410017) ^ 69205008 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 138410017) ^ 46136672 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 138410017) ^ 96 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_152625749 : Nat.Prime 152625749 := by
  apply lucas_primality 152625749 (2 : ZMod 152625749)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (43, 1), (80669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (43, 1), (80669, 1)] : List FactorBlock).map factorBlockValue).prod) = 152625749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_43
      · exact prime_oneHundredFortySixEN_80669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 152625749) ^ 76312874 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 152625749) ^ 13875068 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 152625749) ^ 3549436 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 152625749) ^ 1892 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_164299337 : Nat.Prime 164299337 := by
  apply lucas_primality 164299337 (3 : ZMod 164299337)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1163, 1), (17659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1163, 1), (17659, 1)] : List FactorBlock).map factorBlockValue).prod) = 164299337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_1163
      · exact prime_oneHundredFortySixEN_17659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 164299337) ^ 82149668 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 164299337) ^ 141272 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 164299337) ^ 9304 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_179794273 : Nat.Prime 179794273 := by
  apply lucas_primality 179794273 (15 : ZMod 179794273)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (267551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (267551, 1)] : List FactorBlock).map factorBlockValue).prod) = 179794273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_267551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 179794273) ^ 89897136 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (15 : ZMod 179794273) ^ 59931424 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (15 : ZMod 179794273) ^ 25684896 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (15 : ZMod 179794273) ^ 672 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_192894067 : Nat.Prime 192894067 := by
  apply lucas_primality 192894067 (3 : ZMod 192894067)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1301, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1301, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) = 192894067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_1301
      · exact prime_oneHundredFortySixEN_8237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 192894067) ^ 96447033 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 192894067) ^ 64298022 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 192894067) ^ 148266 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 192894067) ^ 23418 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_199293937 : Nat.Prime 199293937 := by
  apply lucas_primality 199293937 (5 : ZMod 199293937)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (683, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (683, 1), (6079, 1)] : List FactorBlock).map factorBlockValue).prod) = 199293937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_683
      · exact prime_oneHundredFortySixEN_6079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 199293937) ^ 99646968 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 199293937) ^ 66431312 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 199293937) ^ 291792 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 199293937) ^ 32784 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_203548823 : Nat.Prime 203548823 := by
  apply lucas_primality 203548823 (5 : ZMod 203548823)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (2165413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (2165413, 1)] : List FactorBlock).map factorBlockValue).prod) = 203548823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_47
      · exact prime_oneHundredFortySixEN_2165413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 203548823) ^ 101774411 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 203548823) ^ 4330826 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 203548823) ^ 94 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_211045273 : Nat.Prime 211045273 := by
  apply lucas_primality 211045273 (5 : ZMod 211045273)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (419, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (419, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 211045273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_419
      · exact prime_oneHundredFortySixEN_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 211045273) ^ 105522636 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 211045273) ^ 70348424 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 211045273) ^ 6807912 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 211045273) ^ 503688 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 211045273) ^ 311736 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_226866709 : Nat.Prime 226866709 := by
  apply lucas_primality 226866709 (2 : ZMod 226866709)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (6301853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (6301853, 1)] : List FactorBlock).map factorBlockValue).prod) = 226866709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_6301853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 226866709) ^ 113433354 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 226866709) ^ 75622236 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 226866709) ^ 36 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_249675781 : Nat.Prime 249675781 := by
  apply lucas_primality 249675781 (10 : ZMod 249675781)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (4161263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (4161263, 1)] : List FactorBlock).map factorBlockValue).prod) = 249675781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_4161263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 249675781) ^ 124837890 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 249675781) ^ 83225260 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 249675781) ^ 49935156 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 249675781) ^ 60 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_290012837 : Nat.Prime 290012837 := by
  apply lucas_primality 290012837 (2 : ZMod 290012837)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (547, 1), (132547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (547, 1), (132547, 1)] : List FactorBlock).map factorBlockValue).prod) = 290012837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_547
      · exact prime_oneHundredFortySixEN_132547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 290012837) ^ 145006418 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 290012837) ^ 530188 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 290012837) ^ 2188 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_305069927 : Nat.Prime 305069927 := by
  apply lucas_primality 305069927 (5 : ZMod 305069927)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1933, 1), (11273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1933, 1), (11273, 1)] : List FactorBlock).map factorBlockValue).prod) = 305069927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_1933
      · exact prime_oneHundredFortySixEN_11273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 305069927) ^ 152534963 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 305069927) ^ 43581418 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 305069927) ^ 157822 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 305069927) ^ 27062 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_311725933 : Nat.Prime 311725933 := by
  apply lucas_primality 311725933 (5 : ZMod 311725933)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19, 1), (173, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19, 1), (173, 1), (1129, 1)] : List FactorBlock).map factorBlockValue).prod) = 311725933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_173
      · exact prime_oneHundredFortySixEN_1129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 311725933) ^ 155862966 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 311725933) ^ 103908644 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 311725933) ^ 44532276 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 311725933) ^ 16406628 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 311725933) ^ 1801884 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 311725933) ^ 276108 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_359041283 : Nat.Prime 359041283 := by
  apply lucas_primality 359041283 (2 : ZMod 359041283)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (991, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (991, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) = 359041283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_107
      · exact prime_oneHundredFortySixEN_991
      · exact prime_oneHundredFortySixEN_1693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 359041283) ^ 179520641 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 359041283) ^ 3355526 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 359041283) ^ 362302 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 359041283) ^ 212074 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_513784801 : Nat.Prime 513784801 := by
  apply lucas_primality 513784801 (17 : ZMod 513784801)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 2), (71359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 2), (71359, 1)] : List FactorBlock).map factorBlockValue).prod) = 513784801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_71359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 513784801) ^ 256892400 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 513784801) ^ 171261600 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 513784801) ^ 102756960 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 513784801) ^ 7200 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_516616267 : Nat.Prime 516616267 := by
  apply lucas_primality 516616267 (2 : ZMod 516616267)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (2969059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (2969059, 1)] : List FactorBlock).map factorBlockValue).prod) = 516616267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_29
      · exact prime_oneHundredFortySixEN_2969059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 516616267) ^ 258308133 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 516616267) ^ 172205422 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 516616267) ^ 17814354 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 516616267) ^ 174 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_610241131 : Nat.Prime 610241131 := by
  apply lucas_primality 610241131 (2 : ZMod 610241131)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (41, 1), (59, 1), (2803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (41, 1), (59, 1), (2803, 1)] : List FactorBlock).map factorBlockValue).prod) = 610241131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_41
      · exact prime_oneHundredFortySixEN_59
      · exact prime_oneHundredFortySixEN_2803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 610241131) ^ 305120565 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 610241131) ^ 203413710 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 610241131) ^ 122048226 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 610241131) ^ 14883930 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 610241131) ^ 10343070 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 610241131) ^ 217710 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_17203
      · exact prime_oneHundredFortySixEN_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_719714939 : Nat.Prime 719714939 := by
  apply lucas_primality 719714939 (2 : ZMod 719714939)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (5371007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (5371007, 1)] : List FactorBlock).map factorBlockValue).prod) = 719714939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_67
      · exact prime_oneHundredFortySixEN_5371007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 719714939) ^ 359857469 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 719714939) ^ 10742014 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 719714939) ^ 134 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_866013149 : Nat.Prime 866013149 := by
  apply lucas_primality 866013149 (2 : ZMod 866013149)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (13, 1), (31, 1), (6977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (13, 1), (31, 1), (6977, 1)] : List FactorBlock).map factorBlockValue).prod) = 866013149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_6977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 866013149) ^ 433006574 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 866013149) ^ 123716164 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 866013149) ^ 78728468 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 866013149) ^ 66616396 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 866013149) ^ 27935908 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 866013149) ^ 124124 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_907466837 : Nat.Prime 907466837 := by
  apply lucas_primality 907466837 (2 : ZMod 907466837)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (226866709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (226866709, 1)] : List FactorBlock).map factorBlockValue).prod) = 907466837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_226866709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 907466837) ^ 453733418 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 907466837) ^ 4 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1138292633 : Nat.Prime 1138292633 := by
  apply lucas_primality 1138292633 (3 : ZMod 1138292633)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (1499, 1), (4127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (1499, 1), (4127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1138292633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_1499
      · exact prime_oneHundredFortySixEN_4127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1138292633) ^ 569146316 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1138292633) ^ 49490984 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1138292633) ^ 759368 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1138292633) ^ 275816 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1255565303 : Nat.Prime 1255565303 := by
  apply lucas_primality 1255565303 (5 : ZMod 1255565303)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (4157501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (4157501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1255565303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_151
      · exact prime_oneHundredFortySixEN_4157501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1255565303) ^ 627782651 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 1255565303) ^ 8315002 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 1255565303) ^ 302 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1273359487 : Nat.Prime 1273359487 := by
  apply lucas_primality 1273359487 (5 : ZMod 1273359487)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (30318083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (30318083, 1)] : List FactorBlock).map factorBlockValue).prod) = 1273359487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_30318083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1273359487) ^ 636679743 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 1273359487) ^ 424453162 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 1273359487) ^ 181908498 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 1273359487) ^ 42 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1321482263 : Nat.Prime 1321482263 := by
  apply lucas_primality 1321482263 (5 : ZMod 1321482263)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (2309, 1), (15061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (2309, 1), (15061, 1)] : List FactorBlock).map factorBlockValue).prod) = 1321482263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_2309
      · exact prime_oneHundredFortySixEN_15061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1321482263) ^ 660741131 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 1321482263) ^ 69551698 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 1321482263) ^ 572318 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 1321482263) ^ 87742 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1326020117 : Nat.Prime 1326020117 := by
  apply lucas_primality 1326020117 (2 : ZMod 1326020117)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (157, 1), (2111497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (157, 1), (2111497, 1)] : List FactorBlock).map factorBlockValue).prod) = 1326020117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_157
      · exact prime_oneHundredFortySixEN_2111497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1326020117) ^ 663010058 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1326020117) ^ 8445988 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1326020117) ^ 628 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1355212589 : Nat.Prime 1355212589 := by
  apply lucas_primality 1355212589 (2 : ZMod 1355212589)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (4641139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (4641139, 1)] : List FactorBlock).map factorBlockValue).prod) = 1355212589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_73
      · exact prime_oneHundredFortySixEN_4641139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1355212589) ^ 677606294 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1355212589) ^ 18564556 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1355212589) ^ 292 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1508257937 : Nat.Prime 1508257937 := by
  apply lucas_primality 1508257937 (3 : ZMod 1508257937)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (37, 1), (110771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (37, 1), (110771, 1)] : List FactorBlock).map factorBlockValue).prod) = 1508257937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_37
      · exact prime_oneHundredFortySixEN_110771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1508257937) ^ 754128968 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508257937) ^ 65576432 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508257937) ^ 40763728 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508257937) ^ 13616 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1751636149 : Nat.Prime 1751636149 := by
  apply lucas_primality 1751636149 (2 : ZMod 1751636149)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1433, 1), (101863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1433, 1), (101863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1751636149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_1433
      · exact prime_oneHundredFortySixEN_101863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1751636149) ^ 875818074 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1751636149) ^ 583878716 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1751636149) ^ 1222356 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1751636149) ^ 17196 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1928564951 : Nat.Prime 1928564951 := by
  apply lucas_primality 1928564951 (11 : ZMod 1928564951)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (23, 1), (129001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (23, 1), (129001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1928564951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_129001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1928564951) ^ 964282475 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 1928564951) ^ 385712990 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 1928564951) ^ 148351150 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 1928564951) ^ 83850650 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 1928564951) ^ 14950 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1953514001 : Nat.Prime 1953514001 := by
  apply lucas_primality 1953514001 (3 : ZMod 1953514001)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (127, 1), (7691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (127, 1), (7691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1953514001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_127
      · exact prime_oneHundredFortySixEN_7691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1953514001) ^ 976757000 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953514001) ^ 390702800 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953514001) ^ 15382000 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953514001) ^ 254000 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1976634587 : Nat.Prime 1976634587 := by
  apply lucas_primality 1976634587 (2 : ZMod 1976634587)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (31881203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (31881203, 1)] : List FactorBlock).map factorBlockValue).prod) = 1976634587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_31881203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1976634587) ^ 988317293 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1976634587) ^ 63762406 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1976634587) ^ 62 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2052258671 : Nat.Prime 2052258671 := by
  apply lucas_primality 2052258671 (11 : ZMod 2052258671)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (11, 1), (380753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (11, 1), (380753, 1)] : List FactorBlock).map factorBlockValue).prod) = 2052258671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_380753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2052258671) ^ 1026129335 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 2052258671) ^ 410451734 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 2052258671) ^ 293179810 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 2052258671) ^ 186568970 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 2052258671) ^ 5390 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2066465069 : Nat.Prime 2066465069 := by
  apply lucas_primality 2066465069 (2 : ZMod 2066465069)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (516616267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (516616267, 1)] : List FactorBlock).map factorBlockValue).prod) = 2066465069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_516616267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2066465069) ^ 1033232534 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2066465069) ^ 4 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2083077641 : Nat.Prime 2083077641 := by
  apply lucas_primality 2083077641 (6 : ZMod 2083077641)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (293, 1), (25391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (293, 1), (25391, 1)] : List FactorBlock).map factorBlockValue).prod) = 2083077641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_293
      · exact prime_oneHundredFortySixEN_25391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2083077641) ^ 1041538820 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 2083077641) ^ 416615528 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 2083077641) ^ 297582520 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 2083077641) ^ 7109480 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 2083077641) ^ 82040 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2756301673 : Nat.Prime 2756301673 := by
  apply lucas_primality 2756301673 (5 : ZMod 2756301673)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1553, 1), (73951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1553, 1), (73951, 1)] : List FactorBlock).map factorBlockValue).prod) = 2756301673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_1553
      · exact prime_oneHundredFortySixEN_73951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2756301673) ^ 1378150836 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 2756301673) ^ 918767224 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 2756301673) ^ 1774824 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 2756301673) ^ 37272 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2937287917 : Nat.Prime 2937287917 := by
  apply lucas_primality 2937287917 (5 : ZMod 2937287917)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1217, 1), (67043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1217, 1), (67043, 1)] : List FactorBlock).map factorBlockValue).prod) = 2937287917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_1217
      · exact prime_oneHundredFortySixEN_67043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2937287917) ^ 1468643958 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 2937287917) ^ 979095972 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 2937287917) ^ 2413548 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 2937287917) ^ 43812 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2950070987 : Nat.Prime 2950070987 := by
  apply lucas_primality 2950070987 (2 : ZMod 2950070987)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (43, 1), (449, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (43, 1), (449, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) = 2950070987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_43
      · exact prime_oneHundredFortySixEN_449
      · exact prime_oneHundredFortySixEN_4021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2950070987) ^ 1475035493 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2950070987) ^ 155266894 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2950070987) ^ 68606302 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2950070987) ^ 6570314 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2950070987) ^ 733666 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_3907028003 : Nat.Prime 3907028003 := by
  apply lucas_primality 3907028003 (2 : ZMod 3907028003)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1953514001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1953514001, 1)] : List FactorBlock).map factorBlockValue).prod) = 3907028003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_1953514001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3907028003) ^ 1953514001 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 3907028003) ^ 2 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_4154264579 : Nat.Prime 4154264579 := by
  apply lucas_primality 4154264579 (2 : ZMod 4154264579)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (179, 1), (181, 1), (1051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (179, 1), (181, 1), (1051, 1)] : List FactorBlock).map factorBlockValue).prod) = 4154264579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_61
      · exact prime_oneHundredFortySixEN_179
      · exact prime_oneHundredFortySixEN_181
      · exact prime_oneHundredFortySixEN_1051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4154264579) ^ 2077132289 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4154264579) ^ 68102698 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4154264579) ^ 23208182 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4154264579) ^ 22951738 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4154264579) ^ 3952678 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_4394180647 : Nat.Prime 4394180647 := by
  apply lucas_primality 4394180647 (3 : ZMod 4394180647)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (701, 1), (348247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (701, 1), (348247, 1)] : List FactorBlock).map factorBlockValue).prod) = 4394180647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_701
      · exact prime_oneHundredFortySixEN_348247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4394180647) ^ 2197090323 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 4394180647) ^ 1464726882 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 4394180647) ^ 6268446 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 4394180647) ^ 12618 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_4639425031 : Nat.Prime 4639425031 := by
  apply lucas_primality 4639425031 (3 : ZMod 4639425031)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1481, 1), (34807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1481, 1), (34807, 1)] : List FactorBlock).map factorBlockValue).prod) = 4639425031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_1481
      · exact prime_oneHundredFortySixEN_34807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4639425031) ^ 2319712515 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 4639425031) ^ 1546475010 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 4639425031) ^ 927885006 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 4639425031) ^ 3132630 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 4639425031) ^ 133290 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_4901438579 : Nat.Prime 4901438579 := by
  apply lucas_primality 4901438579 (2 : ZMod 4901438579)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (373, 1), (41849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (373, 1), (41849, 1)] : List FactorBlock).map factorBlockValue).prod) = 4901438579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_157
      · exact prime_oneHundredFortySixEN_373
      · exact prime_oneHundredFortySixEN_41849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4901438579) ^ 2450719289 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4901438579) ^ 31219354 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4901438579) ^ 13140586 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4901438579) ^ 117122 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_5250589049 : Nat.Prime 5250589049 := by
  apply lucas_primality 5250589049 (3 : ZMod 5250589049)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 2), (97, 1), (18743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 2), (97, 1), (18743, 1)] : List FactorBlock).map factorBlockValue).prod) = 5250589049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_97
      · exact prime_oneHundredFortySixEN_18743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5250589049) ^ 2625294524 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 5250589049) ^ 276346792 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 5250589049) ^ 54129784 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 5250589049) ^ 280136 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_5416177727 : Nat.Prime 5416177727 := by
  apply lucas_primality 5416177727 (5 : ZMod 5416177727)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3259, 1), (830957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3259, 1), (830957, 1)] : List FactorBlock).map factorBlockValue).prod) = 5416177727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3259
      · exact prime_oneHundredFortySixEN_830957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5416177727) ^ 2708088863 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 5416177727) ^ 1661914 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 5416177727) ^ 6518 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_5568263069 : Nat.Prime 5568263069 := by
  apply lucas_primality 5568263069 (2 : ZMod 5568263069)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (20777101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (20777101, 1)] : List FactorBlock).map factorBlockValue).prod) = 5568263069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_67
      · exact prime_oneHundredFortySixEN_20777101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5568263069) ^ 2784131534 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 5568263069) ^ 83108404 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 5568263069) ^ 268 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_6033103019 : Nat.Prime 6033103019 := by
  apply lucas_primality 6033103019 (2 : ZMod 6033103019)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (233, 1), (275459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (233, 1), (275459, 1)] : List FactorBlock).map factorBlockValue).prod) = 6033103019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_47
      · exact prime_oneHundredFortySixEN_233
      · exact prime_oneHundredFortySixEN_275459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6033103019) ^ 3016551509 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 6033103019) ^ 128363894 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 6033103019) ^ 25893146 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 6033103019) ^ 21902 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_7057559941 : Nat.Prime 7057559941 := by
  apply lucas_primality 7057559941 (7 : ZMod 7057559941)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (59, 1), (1993661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (59, 1), (1993661, 1)] : List FactorBlock).map factorBlockValue).prod) = 7057559941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_59
      · exact prime_oneHundredFortySixEN_1993661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7057559941) ^ 3528779970 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 7057559941) ^ 2352519980 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 7057559941) ^ 1411511988 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 7057559941) ^ 119619660 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 7057559941) ^ 3540 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_7894049159 : Nat.Prime 7894049159 := by
  apply lucas_primality 7894049159 (31 : ZMod 7894049159)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (47554513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (47554513, 1)] : List FactorBlock).map factorBlockValue).prod) = 7894049159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_83
      · exact prime_oneHundredFortySixEN_47554513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (31 : ZMod 7894049159) ^ 3947024579 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (31 : ZMod 7894049159) ^ 95109026 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (31 : ZMod 7894049159) ^ 166 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_7905327041 : Nat.Prime 7905327041 := by
  apply lucas_primality 7905327041 (3 : ZMod 7905327041)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (13, 1), (181, 1), (10499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (13, 1), (181, 1), (10499, 1)] : List FactorBlock).map factorBlockValue).prod) = 7905327041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_181
      · exact prime_oneHundredFortySixEN_10499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7905327041) ^ 3952663520 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 7905327041) ^ 1581065408 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 7905327041) ^ 608102080 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 7905327041) ^ 43675840 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 7905327041) ^ 752960 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_8366161637 : Nat.Prime 8366161637 := by
  apply lucas_primality 8366161637 (2 : ZMod 8366161637)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (3613, 1), (82699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (3613, 1), (82699, 1)] : List FactorBlock).map factorBlockValue).prod) = 8366161637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_3613
      · exact prime_oneHundredFortySixEN_82699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8366161637) ^ 4183080818 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 8366161637) ^ 1195165948 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 8366161637) ^ 2315572 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 8366161637) ^ 101164 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_9071138863 : Nat.Prime 9071138863 := by
  apply lucas_primality 9071138863 (6 : ZMod 9071138863)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (337, 1), (498469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (337, 1), (498469, 1)] : List FactorBlock).map factorBlockValue).prod) = 9071138863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_337
      · exact prime_oneHundredFortySixEN_498469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 9071138863) ^ 4535569431 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 9071138863) ^ 3023712954 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 9071138863) ^ 26917326 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 9071138863) ^ 18198 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_9802017359 : Nat.Prime 9802017359 := by
  apply lucas_primality 9802017359 (7 : ZMod 9802017359)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4013, 1), (174469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4013, 1), (174469, 1)] : List FactorBlock).map factorBlockValue).prod) = 9802017359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_4013
      · exact prime_oneHundredFortySixEN_174469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 9802017359) ^ 4901008679 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 9802017359) ^ 1400288194 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 9802017359) ^ 2442566 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 9802017359) ^ 56182 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_11968849817 : Nat.Prime 11968849817 := by
  apply lucas_primality 11968849817 (3 : ZMod 11968849817)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (19, 1), (1022629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (19, 1), (1022629, 1)] : List FactorBlock).map factorBlockValue).prod) = 11968849817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_1022629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11968849817) ^ 5984424908 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 11968849817) ^ 1709835688 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 11968849817) ^ 1088077256 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 11968849817) ^ 629939464 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 11968849817) ^ 11704 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_12047165569 : Nat.Prime 12047165569 := by
  apply lucas_primality 12047165569 (7 : ZMod 12047165569)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (10457609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (10457609, 1)] : List FactorBlock).map factorBlockValue).prod) = 12047165569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_10457609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 12047165569) ^ 6023582784 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 12047165569) ^ 4015721856 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 12047165569) ^ 1152 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_12374682521 : Nat.Prime 12374682521 := by
  apply lucas_primality 12374682521 (3 : ZMod 12374682521)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (541, 1), (30097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (541, 1), (30097, 1)] : List FactorBlock).map factorBlockValue).prod) = 12374682521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_541
      · exact prime_oneHundredFortySixEN_30097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12374682521) ^ 6187341260 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 12374682521) ^ 2474936504 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 12374682521) ^ 651299080 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 12374682521) ^ 22873720 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 12374682521) ^ 411160 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_13732339741 : Nat.Prime 13732339741 := by
  apply lucas_primality 13732339741 (2 : ZMod 13732339741)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (691, 1), (47317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (691, 1), (47317, 1)] : List FactorBlock).map factorBlockValue).prod) = 13732339741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_691
      · exact prime_oneHundredFortySixEN_47317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13732339741) ^ 6866169870 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 13732339741) ^ 4577446580 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 13732339741) ^ 2746467948 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 13732339741) ^ 1961762820 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 13732339741) ^ 19873140 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 13732339741) ^ 290220 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_15000758327 : Nat.Prime 15000758327 := by
  apply lucas_primality 15000758327 (5 : ZMod 15000758327)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34511, 1), (217333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34511, 1), (217333, 1)] : List FactorBlock).map factorBlockValue).prod) = 15000758327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_34511
      · exact prime_oneHundredFortySixEN_217333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15000758327) ^ 7500379163 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 15000758327) ^ 434666 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 15000758327) ^ 69022 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_16262551069 : Nat.Prime 16262551069 := by
  apply lucas_primality 16262551069 (2 : ZMod 16262551069)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1355212589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1355212589, 1)] : List FactorBlock).map factorBlockValue).prod) = 16262551069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_1355212589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16262551069) ^ 8131275534 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 16262551069) ^ 5420850356 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 16262551069) ^ 12 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_17032781713 : Nat.Prime 17032781713 := by
  apply lucas_primality 17032781713 (5 : ZMod 17032781713)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (20873507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (20873507, 1)] : List FactorBlock).map factorBlockValue).prod) = 17032781713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_17
      · exact prime_oneHundredFortySixEN_20873507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17032781713) ^ 8516390856 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 17032781713) ^ 5677593904 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 17032781713) ^ 1001928336 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 17032781713) ^ 816 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_17290857239 : Nat.Prime 17290857239 := by
  apply lucas_primality 17290857239 (13 : ZMod 17290857239)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (181, 1), (47764799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (181, 1), (47764799, 1)] : List FactorBlock).map factorBlockValue).prod) = 17290857239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_181
      · exact prime_oneHundredFortySixEN_47764799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 17290857239) ^ 8645428619 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 17290857239) ^ 95529598 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 17290857239) ^ 362 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_18488054993 : Nat.Prime 18488054993 := by
  apply lucas_primality 18488054993 (3 : ZMod 18488054993)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (105045767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (105045767, 1)] : List FactorBlock).map factorBlockValue).prod) = 18488054993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_105045767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 18488054993) ^ 9244027496 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 18488054993) ^ 1680732272 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 18488054993) ^ 176 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_18910048733 : Nat.Prime 18910048733 := by
  apply lucas_primality 18910048733 (2 : ZMod 18910048733)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (97, 1), (113, 1), (13913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (97, 1), (113, 1), (13913, 1)] : List FactorBlock).map factorBlockValue).prod) = 18910048733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_97
      · exact prime_oneHundredFortySixEN_113
      · exact prime_oneHundredFortySixEN_13913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18910048733) ^ 9455024366 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 18910048733) ^ 610001572 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 18910048733) ^ 194948956 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 18910048733) ^ 167345564 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 18910048733) ^ 1359164 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_19203765241 : Nat.Prime 19203765241 := by
  apply lucas_primality 19203765241 (7 : ZMod 19203765241)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (14548307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (14548307, 1)] : List FactorBlock).map factorBlockValue).prod) = 19203765241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_14548307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 19203765241) ^ 9601882620 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 19203765241) ^ 6401255080 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 19203765241) ^ 3840753048 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 19203765241) ^ 1745796840 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 19203765241) ^ 1320 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_22761499907 : Nat.Prime 22761499907 := by
  apply lucas_primality 22761499907 (2 : ZMod 22761499907)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (192894067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (192894067, 1)] : List FactorBlock).map factorBlockValue).prod) = 22761499907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_59
      · exact prime_oneHundredFortySixEN_192894067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22761499907) ^ 11380749953 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 22761499907) ^ 385788134 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 22761499907) ^ 118 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_26911151413 : Nat.Prime 26911151413 := by
  apply lucas_primality 26911151413 (2 : ZMod 26911151413)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (12528469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (12528469, 1)] : List FactorBlock).map factorBlockValue).prod) = 26911151413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_179
      · exact prime_oneHundredFortySixEN_12528469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26911151413) ^ 13455575706 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 26911151413) ^ 8970383804 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 26911151413) ^ 150341628 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 26911151413) ^ 2148 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_27318342241 : Nat.Prime 27318342241 := by
  apply lucas_primality 27318342241 (13 : ZMod 27318342241)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (7, 1), (227, 1), (11939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (7, 1), (227, 1), (11939, 1)] : List FactorBlock).map factorBlockValue).prod) = 27318342241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_227
      · exact prime_oneHundredFortySixEN_11939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 27318342241) ^ 13659171120 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 27318342241) ^ 9106114080 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 27318342241) ^ 5463668448 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 27318342241) ^ 3902620320 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 27318342241) ^ 120345120 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 27318342241) ^ 2288160 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_27836550187 : Nat.Prime 27836550187 := by
  apply lucas_primality 27836550187 (3 : ZMod 27836550187)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4639425031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4639425031, 1)] : List FactorBlock).map factorBlockValue).prod) = 27836550187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_4639425031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 27836550187) ^ 13918275093 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 27836550187) ^ 9278850062 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 27836550187) ^ 6 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_28438035289 : Nat.Prime 28438035289 := by
  apply lucas_primality 28438035289 (7 : ZMod 28438035289)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (91147549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (91147549, 1)] : List FactorBlock).map factorBlockValue).prod) = 28438035289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_91147549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 28438035289) ^ 14219017644 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 28438035289) ^ 9479345096 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 28438035289) ^ 2187541176 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 28438035289) ^ 312 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_41716366297 : Nat.Prime 41716366297 := by
  apply lucas_primality 41716366297 (10 : ZMod 41716366297)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (677, 1), (233407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (677, 1), (233407, 1)] : List FactorBlock).map factorBlockValue).prod) = 41716366297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_677
      · exact prime_oneHundredFortySixEN_233407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 41716366297) ^ 20858183148 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 41716366297) ^ 13905455432 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 41716366297) ^ 3792396936 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 41716366297) ^ 61619448 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 41716366297) ^ 178728 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_50122439863 : Nat.Prime 50122439863 := by
  apply lucas_primality 50122439863 (3 : ZMod 50122439863)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (61, 1), (2207, 1), (5641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (61, 1), (2207, 1), (5641, 1)] : List FactorBlock).map factorBlockValue).prod) = 50122439863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_61
      · exact prime_oneHundredFortySixEN_2207
      · exact prime_oneHundredFortySixEN_5641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 50122439863) ^ 25061219931 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 50122439863) ^ 16707479954 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 50122439863) ^ 4556585442 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 50122439863) ^ 821679342 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 50122439863) ^ 22710666 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 50122439863) ^ 8885382 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_69012017411 : Nat.Prime 69012017411 := by
  apply lucas_primality 69012017411 (10 : ZMod 69012017411)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (1543, 1), (20611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (1543, 1), (20611, 1)] : List FactorBlock).map factorBlockValue).prod) = 69012017411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_1543
      · exact prime_oneHundredFortySixEN_20611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 69012017411) ^ 34506008705 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 69012017411) ^ 13802403482 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 69012017411) ^ 9858859630 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 69012017411) ^ 2226194110 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 69012017411) ^ 44725870 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 69012017411) ^ 3348310 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_83243739661 : Nat.Prime 83243739661 := by
  apply lucas_primality 83243739661 (7 : ZMod 83243739661)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (5309, 1), (261329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (5309, 1), (261329, 1)] : List FactorBlock).map factorBlockValue).prod) = 83243739661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_5309
      · exact prime_oneHundredFortySixEN_261329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 83243739661) ^ 41621869830 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 83243739661) ^ 27747913220 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 83243739661) ^ 16648747932 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 83243739661) ^ 15679740 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 83243739661) ^ 318540 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_90400701817 : Nat.Prime 90400701817 := by
  apply lucas_primality 90400701817 (5 : ZMod 90400701817)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1255565303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1255565303, 1)] : List FactorBlock).map factorBlockValue).prod) = 90400701817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_1255565303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 90400701817) ^ 45200350908 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 90400701817) ^ 30133567272 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 90400701817) ^ 72 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_108172930361 : Nat.Prime 108172930361 := by
  apply lucas_primality 108172930361 (6 : ZMod 108172930361)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 2), (131, 1), (170609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 2), (131, 1), (170609, 1)] : List FactorBlock).map factorBlockValue).prod) = 108172930361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_131
      · exact prime_oneHundredFortySixEN_170609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 108172930361) ^ 54086465180 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 108172930361) ^ 21634586072 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 108172930361) ^ 9833902760 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 108172930361) ^ 825747560 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 108172930361) ^ 634040 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_109548221681 : Nat.Prime 109548221681 := by
  apply lucas_primality 109548221681 (6 : ZMod 109548221681)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (17, 1), (23, 1), (59, 1), (59359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (17, 1), (23, 1), (59, 1), (59359, 1)] : List FactorBlock).map factorBlockValue).prod) = 109548221681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_17
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_59
      · exact prime_oneHundredFortySixEN_59359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 109548221681) ^ 54774110840 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 109548221681) ^ 21909644336 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 109548221681) ^ 6444013040 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 109548221681) ^ 4762966160 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 109548221681) ^ 1856749520 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 109548221681) ^ 1845520 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_117126262919 : Nat.Prime 117126262919 := by
  apply lucas_primality 117126262919 (7 : ZMod 117126262919)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (8366161637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (8366161637, 1)] : List FactorBlock).map factorBlockValue).prod) = 117126262919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_8366161637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 117126262919) ^ 58563131459 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 117126262919) ^ 16732323274 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 117126262919) ^ 14 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_121440509899 : Nat.Prime 121440509899 := by
  apply lucas_primality 121440509899 (2 : ZMod 121440509899)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (331, 1), (6361, 1), (9613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (331, 1), (6361, 1), (9613, 1)] : List FactorBlock).map factorBlockValue).prod) = 121440509899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_331
      · exact prime_oneHundredFortySixEN_6361
      · exact prime_oneHundredFortySixEN_9613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 121440509899) ^ 60720254949 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 121440509899) ^ 40480169966 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 121440509899) ^ 366889758 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 121440509899) ^ 19091418 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 121440509899) ^ 12632946 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_151910698573 : Nat.Prime 151910698573 := by
  apply lucas_primality 151910698573 (2 : ZMod 151910698573)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (37, 1), (97, 1), (1175743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (37, 1), (97, 1), (1175743, 1)] : List FactorBlock).map factorBlockValue).prod) = 151910698573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_37
      · exact prime_oneHundredFortySixEN_97
      · exact prime_oneHundredFortySixEN_1175743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 151910698573) ^ 75955349286 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 151910698573) ^ 50636899524 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 151910698573) ^ 4105694556 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 151910698573) ^ 1566089676 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 151910698573) ^ 129204 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_156846034529 : Nat.Prime 156846034529 := by
  apply lucas_primality 156846034529 (3 : ZMod 156846034529)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (4901438579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (4901438579, 1)] : List FactorBlock).map factorBlockValue).prod) = 156846034529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_4901438579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 156846034529) ^ 78423017264 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 156846034529) ^ 32 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_196453380427 : Nat.Prime 196453380427 := by
  apply lucas_primality 196453380427 (2 : ZMod 196453380427)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (4933, 1), (141221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (4933, 1), (141221, 1)] : List FactorBlock).map factorBlockValue).prod) = 196453380427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_47
      · exact prime_oneHundredFortySixEN_4933
      · exact prime_oneHundredFortySixEN_141221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 196453380427) ^ 98226690213 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 196453380427) ^ 65484460142 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 196453380427) ^ 4179859158 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 196453380427) ^ 39824322 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 196453380427) ^ 1391106 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_201786549229 : Nat.Prime 201786549229 := by
  apply lucas_primality 201786549229 (2 : ZMod 201786549229)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (311, 1), (1638463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (311, 1), (1638463, 1)] : List FactorBlock).map factorBlockValue).prod) = 201786549229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_311
      · exact prime_oneHundredFortySixEN_1638463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 201786549229) ^ 100893274614 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 201786549229) ^ 67262183076 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 201786549229) ^ 18344231748 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 201786549229) ^ 648831348 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 201786549229) ^ 123156 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_221795546653 : Nat.Prime 221795546653 := by
  apply lucas_primality 221795546653 (2 : ZMod 221795546653)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (137, 1), (383, 1), (39139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (137, 1), (383, 1), (39139, 1)] : List FactorBlock).map factorBlockValue).prod) = 221795546653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_137
      · exact prime_oneHundredFortySixEN_383
      · exact prime_oneHundredFortySixEN_39139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 221795546653) ^ 110897773326 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 221795546653) ^ 73931848884 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 221795546653) ^ 1618945596 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 221795546653) ^ 579100644 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 221795546653) ^ 5666868 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_230727500359 : Nat.Prime 230727500359 := by
  apply lucas_primality 230727500359 (3 : ZMod 230727500359)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (1326020117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (1326020117, 1)] : List FactorBlock).map factorBlockValue).prod) = 230727500359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_29
      · exact prime_oneHundredFortySixEN_1326020117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 230727500359) ^ 115363750179 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 230727500359) ^ 76909166786 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 230727500359) ^ 7956120702 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 230727500359) ^ 174 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_257089749703 : Nat.Prime 257089749703 := by
  apply lucas_primality 257089749703 (5 : ZMod 257089749703)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (24251, 1), (92993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (24251, 1), (92993, 1)] : List FactorBlock).map factorBlockValue).prod) = 257089749703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_24251
      · exact prime_oneHundredFortySixEN_92993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 257089749703) ^ 128544874851 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 257089749703) ^ 85696583234 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 257089749703) ^ 13531039458 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 257089749703) ^ 10601202 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 257089749703) ^ 2764614 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_262745422351 : Nat.Prime 262745422351 := by
  apply lucas_primality 262745422351 (3 : ZMod 262745422351)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1751636149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1751636149, 1)] : List FactorBlock).map factorBlockValue).prod) = 262745422351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_1751636149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 262745422351) ^ 131372711175 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 262745422351) ^ 87581807450 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 262745422351) ^ 52549084470 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 262745422351) ^ 150 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_313692069059 : Nat.Prime 313692069059 := by
  apply lucas_primality 313692069059 (2 : ZMod 313692069059)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (156846034529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (156846034529, 1)] : List FactorBlock).map factorBlockValue).prod) = 313692069059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_156846034529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 313692069059) ^ 156846034529 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 313692069059) ^ 2 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_330184024897 : Nat.Prime 330184024897 := by
  apply lucas_primality 330184024897 (5 : ZMod 330184024897)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 1), (89, 1), (1756597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 1), (89, 1), (1756597, 1)] : List FactorBlock).map factorBlockValue).prod) = 330184024897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_89
      · exact prime_oneHundredFortySixEN_1756597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 330184024897) ^ 165092012448 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 330184024897) ^ 110061341632 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 330184024897) ^ 30016729536 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 330184024897) ^ 3709932864 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 330184024897) ^ 187968 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_499462437967 : Nat.Prime 499462437967 := by
  apply lucas_primality 499462437967 (3 : ZMod 499462437967)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83243739661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83243739661, 1)] : List FactorBlock).map factorBlockValue).prod) = 499462437967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_83243739661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 499462437967) ^ 249731218983 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 499462437967) ^ 166487479322 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 499462437967) ^ 6 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_576584650471 : Nat.Prime 576584650471 := by
  apply lucas_primality 576584650471 (3 : ZMod 576584650471)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (71, 1), (1249, 1), (216731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (71, 1), (1249, 1), (216731, 1)] : List FactorBlock).map factorBlockValue).prod) = 576584650471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_71
      · exact prime_oneHundredFortySixEN_1249
      · exact prime_oneHundredFortySixEN_216731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 576584650471) ^ 288292325235 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 576584650471) ^ 192194883490 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 576584650471) ^ 115316930094 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 576584650471) ^ 8120910570 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 576584650471) ^ 461637030 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 576584650471) ^ 2660370 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_632180375501 : Nat.Prime 632180375501 := by
  apply lucas_primality 632180375501 (2 : ZMod 632180375501)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (331, 1), (3819821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (331, 1), (3819821, 1)] : List FactorBlock).map factorBlockValue).prod) = 632180375501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_331
      · exact prime_oneHundredFortySixEN_3819821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 632180375501) ^ 316090187750 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 632180375501) ^ 126436075100 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 632180375501) ^ 1909910500 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 632180375501) ^ 165500 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_651950589919 : Nat.Prime 651950589919 := by
  apply lucas_primality 651950589919 (6 : ZMod 651950589919)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (43, 1), (68295683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (43, 1), (68295683, 1)] : List FactorBlock).map factorBlockValue).prod) = 651950589919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_37
      · exact prime_oneHundredFortySixEN_43
      · exact prime_oneHundredFortySixEN_68295683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 651950589919) ^ 325975294959 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 651950589919) ^ 217316863306 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 651950589919) ^ 17620286214 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 651950589919) ^ 15161641626 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 651950589919) ^ 9546 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_695944963177 : Nat.Prime 695944963177 := by
  apply lucas_primality 695944963177 (5 : ZMod 695944963177)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1499, 1), (3779, 1), (5119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1499, 1), (3779, 1), (5119, 1)] : List FactorBlock).map factorBlockValue).prod) = 695944963177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_1499
      · exact prime_oneHundredFortySixEN_3779
      · exact prime_oneHundredFortySixEN_5119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 695944963177) ^ 347972481588 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 695944963177) ^ 231981654392 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 695944963177) ^ 464272824 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 695944963177) ^ 184161144 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 695944963177) ^ 135953304 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1172981257421 : Nat.Prime 1172981257421 := by
  apply lucas_primality 1172981257421 (2 : ZMod 1172981257421)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (577, 1), (937, 1), (15497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (577, 1), (937, 1), (15497, 1)] : List FactorBlock).map factorBlockValue).prod) = 1172981257421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_577
      · exact prime_oneHundredFortySixEN_937
      · exact prime_oneHundredFortySixEN_15497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1172981257421) ^ 586490628710 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172981257421) ^ 234596251484 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172981257421) ^ 167568751060 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172981257421) ^ 2032896460 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172981257421) ^ 1251847660 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1172981257421) ^ 75690860 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1378019214431 : Nat.Prime 1378019214431 := by
  apply lucas_primality 1378019214431 (13 : ZMod 1378019214431)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (71, 1), (163, 1), (700423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (71, 1), (163, 1), (700423, 1)] : List FactorBlock).map factorBlockValue).prod) = 1378019214431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_17
      · exact prime_oneHundredFortySixEN_71
      · exact prime_oneHundredFortySixEN_163
      · exact prime_oneHundredFortySixEN_700423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1378019214431) ^ 689009607215 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 1378019214431) ^ 275603842886 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 1378019214431) ^ 81059953790 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 1378019214431) ^ 19408721330 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 1378019214431) ^ 8454105610 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 1378019214431) ^ 1967410 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1417791603323 : Nat.Prime 1417791603323 := by
  apply lucas_primality 1417791603323 (2 : ZMod 1417791603323)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (1279, 1), (9394201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (1279, 1), (9394201, 1)] : List FactorBlock).map factorBlockValue).prod) = 1417791603323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_59
      · exact prime_oneHundredFortySixEN_1279
      · exact prime_oneHundredFortySixEN_9394201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1417791603323) ^ 708895801661 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1417791603323) ^ 24030366158 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1417791603323) ^ 1108515718 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1417791603323) ^ 150922 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1499885932877 : Nat.Prime 1499885932877 := by
  apply lucas_primality 1499885932877 (2 : ZMod 1499885932877)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (521, 1), (719714939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (521, 1), (719714939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1499885932877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_521
      · exact prime_oneHundredFortySixEN_719714939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1499885932877) ^ 749942966438 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1499885932877) ^ 2878859756 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1499885932877) ^ 2084 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1787743018123 : Nat.Prime 1787743018123 := by
  apply lucas_primality 1787743018123 (23 : ZMod 1787743018123)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (2950070987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (2950070987, 1)] : List FactorBlock).map factorBlockValue).prod) = 1787743018123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_101
      · exact prime_oneHundredFortySixEN_2950070987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 1787743018123) ^ 893871509061 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 1787743018123) ^ 595914339374 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 1787743018123) ^ 17700425922 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 1787743018123) ^ 606 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1955189618563 : Nat.Prime 1955189618563 := by
  apply lucas_primality 1955189618563 (3 : ZMod 1955189618563)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (2551, 1), (1616963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (2551, 1), (1616963, 1)] : List FactorBlock).map factorBlockValue).prod) = 1955189618563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_79
      · exact prime_oneHundredFortySixEN_2551
      · exact prime_oneHundredFortySixEN_1616963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1955189618563) ^ 977594809281 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1955189618563) ^ 651729872854 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1955189618563) ^ 24749235678 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1955189618563) ^ 766440462 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1955189618563) ^ 1209174 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2305632233699 : Nat.Prime 2305632233699 := by
  apply lucas_primality 2305632233699 (2 : ZMod 2305632233699)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (50122439863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (50122439863, 1)] : List FactorBlock).map factorBlockValue).prod) = 2305632233699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_50122439863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2305632233699) ^ 1152816116849 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2305632233699) ^ 100244879726 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2305632233699) ^ 46 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2549184599327 : Nat.Prime 2549184599327 := by
  apply lucas_primality 2549184599327 (5 : ZMod 2549184599327)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (12374682521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (12374682521, 1)] : List FactorBlock).map factorBlockValue).prod) = 2549184599327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_103
      · exact prime_oneHundredFortySixEN_12374682521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2549184599327) ^ 1274592299663 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 2549184599327) ^ 24749365042 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 2549184599327) ^ 206 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_3113577818033 : Nat.Prime 3113577818033 := by
  apply lucas_primality 3113577818033 (3 : ZMod 3113577818033)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (61, 1), (290012837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (61, 1), (290012837, 1)] : List FactorBlock).map factorBlockValue).prod) = 3113577818033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_61
      · exact prime_oneHundredFortySixEN_290012837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3113577818033) ^ 1556788909016 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 3113577818033) ^ 283052528912 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 3113577818033) ^ 51042259312 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 3113577818033) ^ 10736 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_3485318574149 : Nat.Prime 3485318574149 := by
  apply lucas_primality 3485318574149 (2 : ZMod 3485318574149)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (59, 1), (61, 1), (157, 1), (277, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (59, 1), (61, 1), (157, 1), (277, 1), (293, 1)] : List FactorBlock).map factorBlockValue).prod) = 3485318574149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_59
      · exact prime_oneHundredFortySixEN_61
      · exact prime_oneHundredFortySixEN_157
      · exact prime_oneHundredFortySixEN_277
      · exact prime_oneHundredFortySixEN_293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3485318574149) ^ 1742659287074 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 3485318574149) ^ 183437819692 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 3485318574149) ^ 59073196172 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 3485318574149) ^ 57136370068 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 3485318574149) ^ 22199481364 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 3485318574149) ^ 12582377524 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 3485318574149) ^ 11895285236 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_3504876155549 : Nat.Prime 3504876155549 := by
  apply lucas_primality 3504876155549 (2 : ZMod 3504876155549)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (241069, 1), (3634723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (241069, 1), (3634723, 1)] : List FactorBlock).map factorBlockValue).prod) = 3504876155549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_241069
      · exact prime_oneHundredFortySixEN_3634723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3504876155549) ^ 1752438077774 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 3504876155549) ^ 14538892 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 3504876155549) ^ 964276 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_3512758070999 : Nat.Prime 3512758070999 := by
  apply lucas_primality 3512758070999 (7 : ZMod 3512758070999)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (337, 1), (1423, 1), (30269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (337, 1), (1423, 1), (30269, 1)] : List FactorBlock).map factorBlockValue).prod) = 3512758070999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_337
      · exact prime_oneHundredFortySixEN_1423
      · exact prime_oneHundredFortySixEN_30269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3512758070999) ^ 1756379035499 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 3512758070999) ^ 319341642818 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 3512758070999) ^ 10423614454 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 3512758070999) ^ 2468558026 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 3512758070999) ^ 116051342 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_4103036564533 : Nat.Prime 4103036564533 := by
  apply lucas_primality 4103036564533 (2 : ZMod 4103036564533)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (353, 1), (449, 1), (1153, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (353, 1), (449, 1), (1153, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) = 4103036564533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_353
      · exact prime_oneHundredFortySixEN_449
      · exact prime_oneHundredFortySixEN_1153
      · exact prime_oneHundredFortySixEN_1871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4103036564533) ^ 2051518282266 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103036564533) ^ 1367678854844 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103036564533) ^ 11623333044 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103036564533) ^ 9138166068 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103036564533) ^ 3558574644 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103036564533) ^ 2192964492 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_5245753781063 : Nat.Prime 5245753781063 := by
  apply lucas_primality 5245753781063 (5 : ZMod 5245753781063)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (13732339741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (13732339741, 1)] : List FactorBlock).map factorBlockValue).prod) = 5245753781063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_191
      · exact prime_oneHundredFortySixEN_13732339741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5245753781063) ^ 2622876890531 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 5245753781063) ^ 27464679482 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 5245753781063) ^ 382 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_5781103537171 : Nat.Prime 5781103537171 := by
  apply lucas_primality 5781103537171 (7 : ZMod 5781103537171)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (109, 1), (499, 1), (272533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (109, 1), (499, 1), (272533, 1)] : List FactorBlock).map factorBlockValue).prod) = 5781103537171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_109
      · exact prime_oneHundredFortySixEN_499
      · exact prime_oneHundredFortySixEN_272533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5781103537171) ^ 2890551768585 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 5781103537171) ^ 1927034512390 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 5781103537171) ^ 1156220707434 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 5781103537171) ^ 444700272090 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 5781103537171) ^ 53037647130 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 5781103537171) ^ 11585377830 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 5781103537171) ^ 21212490 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_6673147470247 : Nat.Prime 6673147470247 := by
  apply lucas_primality 6673147470247 (3 : ZMod 6673147470247)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (281, 1), (38891, 1), (101771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (281, 1), (38891, 1), (101771, 1)] : List FactorBlock).map factorBlockValue).prod) = 6673147470247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_281
      · exact prime_oneHundredFortySixEN_38891
      · exact prime_oneHundredFortySixEN_101771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6673147470247) ^ 3336573735123 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 6673147470247) ^ 2224382490082 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 6673147470247) ^ 23747855766 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 6673147470247) ^ 171585906 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 6673147470247) ^ 65570226 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_6852861675739 : Nat.Prime 6852861675739 := by
  apply lucas_primality 6852861675739 (3 : ZMod 6852861675739)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (19, 1), (513784801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (19, 1), (513784801, 1)] : List FactorBlock).map factorBlockValue).prod) = 6852861675739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_513784801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6852861675739) ^ 3426430837869 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 6852861675739) ^ 2284287225246 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 6852861675739) ^ 527143205826 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 6852861675739) ^ 360676930302 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 6852861675739) ^ 13338 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_7238156970427 : Nat.Prime 7238156970427 := by
  apply lucas_primality 7238156970427 (3 : ZMod 7238156970427)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (22761499907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (22761499907, 1)] : List FactorBlock).map factorBlockValue).prod) = 7238156970427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_53
      · exact prime_oneHundredFortySixEN_22761499907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7238156970427) ^ 3619078485213 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 7238156970427) ^ 2412718990142 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 7238156970427) ^ 136568999442 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 7238156970427) ^ 318 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_7831492197443 : Nat.Prime 7831492197443 := by
  apply lucas_primality 7831492197443 (2 : ZMod 7831492197443)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23833, 1), (164299337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23833, 1), (164299337, 1)] : List FactorBlock).map factorBlockValue).prod) = 7831492197443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_23833
      · exact prime_oneHundredFortySixEN_164299337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7831492197443) ^ 3915746098721 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 7831492197443) ^ 328598674 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 7831492197443) ^ 47666 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_13840272280063 : Nat.Prime 13840272280063 := by
  apply lucas_primality 13840272280063 (3 : ZMod 13840272280063)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (107, 1), (563, 1), (440131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (107, 1), (563, 1), (440131, 1)] : List FactorBlock).map factorBlockValue).prod) = 13840272280063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_29
      · exact prime_oneHundredFortySixEN_107
      · exact prime_oneHundredFortySixEN_563
      · exact prime_oneHundredFortySixEN_440131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13840272280063) ^ 6920136140031 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 13840272280063) ^ 4613424093354 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 13840272280063) ^ 477250768278 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 13840272280063) ^ 129348339066 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 13840272280063) ^ 24583076874 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 13840272280063) ^ 31445802 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_16261776595607 : Nat.Prime 16261776595607 := by
  apply lucas_primality 16261776595607 (5 : ZMod 16261776595607)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (97, 1), (137, 1), (11544359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (97, 1), (137, 1), (11544359, 1)] : List FactorBlock).map factorBlockValue).prod) = 16261776595607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_53
      · exact prime_oneHundredFortySixEN_97
      · exact prime_oneHundredFortySixEN_137
      · exact prime_oneHundredFortySixEN_11544359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16261776595607) ^ 8130888297803 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 16261776595607) ^ 306825973502 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 16261776595607) ^ 167647181398 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 16261776595607) ^ 118699099238 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 16261776595607) ^ 1408634 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_22627521584809 : Nat.Prime 22627521584809 := by
  apply lucas_primality 22627521584809 (17 : ZMod 22627521584809)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (23, 1), (47, 1), (107, 1), (166349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (23, 1), (47, 1), (107, 1), (166349, 1)] : List FactorBlock).map factorBlockValue).prod) = 22627521584809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_47
      · exact prime_oneHundredFortySixEN_107
      · exact prime_oneHundredFortySixEN_166349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 22627521584809) ^ 11313760792404 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 22627521584809) ^ 7542507194936 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 22627521584809) ^ 3232503083544 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 22627521584809) ^ 983805286296 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 22627521584809) ^ 481436629464 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 22627521584809) ^ 211472164344 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 22627521584809) ^ 136024392 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_27328674491317 : Nat.Prime 27328674491317 := by
  apply lucas_primality 27328674491317 (2 : ZMod 27328674491317)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (109, 1), (211045273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (109, 1), (211045273, 1)] : List FactorBlock).map factorBlockValue).prod) = 27328674491317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_109
      · exact prime_oneHundredFortySixEN_211045273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27328674491317) ^ 13664337245658 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 27328674491317) ^ 9109558163772 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 27328674491317) ^ 2484424953756 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 27328674491317) ^ 250721784324 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 27328674491317) ^ 129492 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_28058082337093 : Nat.Prime 28058082337093 := by
  apply lucas_primality 28058082337093 (5 : ZMod 28058082337093)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (24691, 1), (94697401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (24691, 1), (94697401, 1)] : List FactorBlock).map factorBlockValue).prod) = 28058082337093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_24691
      · exact prime_oneHundredFortySixEN_94697401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 28058082337093) ^ 14029041168546 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 28058082337093) ^ 9352694112364 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 28058082337093) ^ 1136368812 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 28058082337093) ^ 296292 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_32777134595407 : Nat.Prime 32777134595407 := by
  apply lucas_primality 32777134595407 (5 : ZMod 32777134595407)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19207, 1), (31602227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19207, 1), (31602227, 1)] : List FactorBlock).map factorBlockValue).prod) = 32777134595407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_19207
      · exact prime_oneHundredFortySixEN_31602227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 32777134595407) ^ 16388567297703 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 32777134595407) ^ 10925711531802 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 32777134595407) ^ 1706520258 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 32777134595407) ^ 1037178 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_42296563098107 : Nat.Prime 42296563098107 := by
  apply lucas_primality 42296563098107 (2 : ZMod 42296563098107)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (149, 1), (293, 1), (28495237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (149, 1), (293, 1), (28495237, 1)] : List FactorBlock).map factorBlockValue).prod) = 42296563098107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_17
      · exact prime_oneHundredFortySixEN_149
      · exact prime_oneHundredFortySixEN_293
      · exact prime_oneHundredFortySixEN_28495237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42296563098107) ^ 21148281549053 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 42296563098107) ^ 2488033123418 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 42296563098107) ^ 283869550994 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 42296563098107) ^ 144356870642 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 42296563098107) ^ 1484338 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_50903237294671 : Nat.Prime 50903237294671 := by
  apply lucas_primality 50903237294671 (3 : ZMod 50903237294671)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1993, 1), (5839, 1), (145807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1993, 1), (5839, 1), (145807, 1)] : List FactorBlock).map factorBlockValue).prod) = 50903237294671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_1993
      · exact prime_oneHundredFortySixEN_5839
      · exact prime_oneHundredFortySixEN_145807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 50903237294671) ^ 25451618647335 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 50903237294671) ^ 16967745764890 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 50903237294671) ^ 10180647458934 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 50903237294671) ^ 25541012190 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 50903237294671) ^ 8717800530 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 50903237294671) ^ 349113810 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_51923006573281 : Nat.Prime 51923006573281 := by
  apply lucas_primality 51923006573281 (11 : ZMod 51923006573281)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (108172930361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (108172930361, 1)] : List FactorBlock).map factorBlockValue).prod) = 51923006573281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_108172930361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 51923006573281) ^ 25961503286640 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 51923006573281) ^ 17307668857760 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 51923006573281) ^ 10384601314656 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 51923006573281) ^ 480 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_65878920945883 : Nat.Prime 65878920945883 := by
  apply lucas_primality 65878920945883 (3 : ZMod 65878920945883)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (43, 1), (75557, 1), (102409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (43, 1), (75557, 1), (102409, 1)] : List FactorBlock).map factorBlockValue).prod) = 65878920945883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_43
      · exact prime_oneHundredFortySixEN_75557
      · exact prime_oneHundredFortySixEN_102409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65878920945883) ^ 32939460472941 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 65878920945883) ^ 21959640315294 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 65878920945883) ^ 5988992813262 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 65878920945883) ^ 1532067928974 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 65878920945883) ^ 871910226 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 65878920945883) ^ 643292298 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_92002086558077 : Nat.Prime 92002086558077 := by
  apply lucas_primality 92002086558077 (3 : ZMod 92002086558077)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (37, 1), (73783, 1), (443431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (37, 1), (73783, 1), (443431, 1)] : List FactorBlock).map factorBlockValue).prod) = 92002086558077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_37
      · exact prime_oneHundredFortySixEN_73783
      · exact prime_oneHundredFortySixEN_443431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 92002086558077) ^ 46001043279038 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 92002086558077) ^ 4842215082004 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 92002086558077) ^ 2486542879948 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 92002086558077) ^ 1246927972 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 92002086558077) ^ 207477796 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_95233683001939 : Nat.Prime 95233683001939 := by
  apply lucas_primality 95233683001939 (2 : ZMod 95233683001939)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (811, 1), (15767, 1), (95483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (811, 1), (15767, 1), (95483, 1)] : List FactorBlock).map factorBlockValue).prod) = 95233683001939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_811
      · exact prime_oneHundredFortySixEN_15767
      · exact prime_oneHundredFortySixEN_95483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 95233683001939) ^ 47616841500969 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 95233683001939) ^ 31744561000646 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 95233683001939) ^ 7325667923226 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 95233683001939) ^ 117427475958 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 95233683001939) ^ 6040063614 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 95233683001939) ^ 997388886 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_106206303084169 : Nat.Prime 106206303084169 := by
  apply lucas_primality 106206303084169 (13 : ZMod 106206303084169)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (632180375501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (632180375501, 1)] : List FactorBlock).map factorBlockValue).prod) = 106206303084169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_632180375501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 106206303084169) ^ 53103151542084 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 106206303084169) ^ 35402101028056 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 106206303084169) ^ 15172329012024 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 106206303084169) ^ 168 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_111828445255403 : Nat.Prime 111828445255403 := by
  apply lucas_primality 111828445255403 (2 : ZMod 111828445255403)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1055489, 1), (52974709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1055489, 1), (52974709, 1)] : List FactorBlock).map factorBlockValue).prod) = 111828445255403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_1055489
      · exact prime_oneHundredFortySixEN_52974709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 111828445255403) ^ 55914222627701 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 111828445255403) ^ 105949418 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 111828445255403) ^ 2110978 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_118410737385001 : Nat.Prime 118410737385001 := by
  apply lucas_primality 118410737385001 (7 : ZMod 118410737385001)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 4), (7894049159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 4), (7894049159, 1)] : List FactorBlock).map factorBlockValue).prod) = 118410737385001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7894049159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 118410737385001) ^ 59205368692500 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 118410737385001) ^ 39470245795000 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 118410737385001) ^ 23682147477000 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 118410737385001) ^ 15000 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_131108538381629 : Nat.Prime 131108538381629 := by
  apply lucas_primality 131108538381629 (2 : ZMod 131108538381629)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (32777134595407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (32777134595407, 1)] : List FactorBlock).map factorBlockValue).prod) = 131108538381629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_32777134595407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 131108538381629) ^ 65554269190814 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 131108538381629) ^ 4 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_132102463962263 : Nat.Prime 132102463962263 := by
  apply lucas_primality 132102463962263 (5 : ZMod 132102463962263)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1569643, 1), (42080417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1569643, 1), (42080417, 1)] : List FactorBlock).map factorBlockValue).prod) = 132102463962263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_1569643
      · exact prime_oneHundredFortySixEN_42080417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 132102463962263) ^ 66051231981131 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 132102463962263) ^ 84160834 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 132102463962263) ^ 3139286 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_150829818654721 : Nat.Prime 150829818654721 := by
  apply lucas_primality 150829818654721 (7 : ZMod 150829818654721)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (3, 1), (5, 1), (31, 1), (47, 1), (127, 1), (13267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (3, 1), (5, 1), (31, 1), (47, 1), (127, 1), (13267, 1)] : List FactorBlock).map factorBlockValue).prod) = 150829818654721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_47
      · exact prime_oneHundredFortySixEN_127
      · exact prime_oneHundredFortySixEN_13267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 150829818654721) ^ 75414909327360 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 150829818654721) ^ 50276606218240 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 150829818654721) ^ 30165963730944 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 150829818654721) ^ 4865478021120 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 150829818654721) ^ 3209145077760 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 150829818654721) ^ 1187636367360 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 150829818654721) ^ 11368796160 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_179535793808563 : Nat.Prime 179535793808563 := by
  apply lucas_primality 179535793808563 (2 : ZMod 179535793808563)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (331, 1), (90400701817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (331, 1), (90400701817, 1)] : List FactorBlock).map factorBlockValue).prod) = 179535793808563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_331
      · exact prime_oneHundredFortySixEN_90400701817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 179535793808563) ^ 89767896904281 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 179535793808563) ^ 59845264602854 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 179535793808563) ^ 542404210902 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 179535793808563) ^ 1986 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_183375342907531 : Nat.Prime 183375342907531 := by
  apply lucas_primality 183375342907531 (10 : ZMod 183375342907531)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (349, 1), (487, 1), (356077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (349, 1), (487, 1), (356077, 1)] : List FactorBlock).map factorBlockValue).prod) = 183375342907531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_101
      · exact prime_oneHundredFortySixEN_349
      · exact prime_oneHundredFortySixEN_487
      · exact prime_oneHundredFortySixEN_356077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 183375342907531) ^ 91687671453765 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 183375342907531) ^ 61125114302510 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 183375342907531) ^ 36675068581506 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 183375342907531) ^ 1815597454530 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 183375342907531) ^ 525430781970 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 183375342907531) ^ 376540745190 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 183375342907531) ^ 514987890 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_217912321619009 : Nat.Prime 217912321619009 := by
  apply lucas_primality 217912321619009 (3 : ZMod 217912321619009)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (195197, 1), (17443301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (195197, 1), (17443301, 1)] : List FactorBlock).map factorBlockValue).prod) = 217912321619009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_195197
      · exact prime_oneHundredFortySixEN_17443301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 217912321619009) ^ 108956160809504 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 217912321619009) ^ 1116371264 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 217912321619009) ^ 12492608 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_218741442542383 : Nat.Prime 218741442542383 := by
  apply lucas_primality 218741442542383 (3 : ZMod 218741442542383)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4019, 1), (9071138863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4019, 1), (9071138863, 1)] : List FactorBlock).map factorBlockValue).prod) = 218741442542383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_4019
      · exact prime_oneHundredFortySixEN_9071138863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 218741442542383) ^ 109370721271191 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 218741442542383) ^ 72913814180794 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 218741442542383) ^ 54426833178 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 218741442542383) ^ 24114 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_257238605397217 : Nat.Prime 257238605397217 := by
  apply lucas_primality 257238605397217 (7 : ZMod 257238605397217)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (4391, 1), (610241131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (4391, 1), (610241131, 1)] : List FactorBlock).map factorBlockValue).prod) = 257238605397217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_4391
      · exact prime_oneHundredFortySixEN_610241131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 257238605397217) ^ 128619302698608 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 257238605397217) ^ 85746201799072 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 257238605397217) ^ 58583148576 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 257238605397217) ^ 421536 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_355883248261133 : Nat.Prime 355883248261133 := by
  apply lucas_primality 355883248261133 (2 : ZMod 355883248261133)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (47, 1), (643, 1), (68465261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (47, 1), (643, 1), (68465261, 1)] : List FactorBlock).map factorBlockValue).prod) = 355883248261133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_43
      · exact prime_oneHundredFortySixEN_47
      · exact prime_oneHundredFortySixEN_643
      · exact prime_oneHundredFortySixEN_68465261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 355883248261133) ^ 177941624130566 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 355883248261133) ^ 8276354610724 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 355883248261133) ^ 7571984005556 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 355883248261133) ^ 553473169924 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 355883248261133) ^ 5198012 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_364044228703567 : Nat.Prime 364044228703567 := by
  apply lucas_primality 364044228703567 (3 : ZMod 364044228703567)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2221, 1), (27318342241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2221, 1), (27318342241, 1)] : List FactorBlock).map factorBlockValue).prod) = 364044228703567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_2221
      · exact prime_oneHundredFortySixEN_27318342241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 364044228703567) ^ 182022114351783 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 364044228703567) ^ 121348076234522 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 364044228703567) ^ 163910053446 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 364044228703567) ^ 13326 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_474148335474823 : Nat.Prime 474148335474823 := by
  apply lucas_primality 474148335474823 (3 : ZMod 474148335474823)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (2549184599327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (2549184599327, 1)] : List FactorBlock).map factorBlockValue).prod) = 474148335474823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_2549184599327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 474148335474823) ^ 237074167737411 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 474148335474823) ^ 158049445158274 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 474148335474823) ^ 15295107595962 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 474148335474823) ^ 186 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_509032372946711 : Nat.Prime 509032372946711 := by
  apply lucas_primality 509032372946711 (11 : ZMod 509032372946711)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (50903237294671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (50903237294671, 1)] : List FactorBlock).map factorBlockValue).prod) = 509032372946711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_50903237294671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 509032372946711) ^ 254516186473355 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 509032372946711) ^ 101806474589342 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 509032372946711) ^ 10 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_525813419822393 : Nat.Prime 525813419822393 := by
  apply lucas_primality 525813419822393 (3 : ZMod 525813419822393)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (19, 1), (2269, 1), (117276293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (19, 1), (2269, 1), (117276293, 1)] : List FactorBlock).map factorBlockValue).prod) = 525813419822393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_2269
      · exact prime_oneHundredFortySixEN_117276293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 525813419822393) ^ 262906709911196 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 525813419822393) ^ 40447186140184 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 525813419822393) ^ 27674390516968 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 525813419822393) ^ 231737954968 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 525813419822393) ^ 4483544 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_572512132654661 : Nat.Prime 572512132654661 := by
  apply lucas_primality 572512132654661 (2 : ZMod 572512132654661)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (19, 1), (109, 1), (179, 1), (7019867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (19, 1), (109, 1), (179, 1), (7019867, 1)] : List FactorBlock).map factorBlockValue).prod) = 572512132654661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_109
      · exact prime_oneHundredFortySixEN_179
      · exact prime_oneHundredFortySixEN_7019867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 572512132654661) ^ 286256066327330 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 572512132654661) ^ 114502426530932 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 572512132654661) ^ 52046557514060 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 572512132654661) ^ 30132217508140 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 572512132654661) ^ 5252404886740 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 572512132654661) ^ 3198391802540 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 572512132654661) ^ 81555980 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_596954601285047 : Nat.Prime 596954601285047 := by
  apply lucas_primality 596954601285047 (5 : ZMod 596954601285047)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (199, 1), (1499885932877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (199, 1), (1499885932877, 1)] : List FactorBlock).map factorBlockValue).prod) = 596954601285047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_199
      · exact prime_oneHundredFortySixEN_1499885932877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 596954601285047) ^ 298477300642523 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 596954601285047) ^ 2999771865754 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 596954601285047) ^ 398 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_663107470323007 : Nat.Prime 663107470323007 := by
  apply lucas_primality 663107470323007 (3 : ZMod 663107470323007)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1218821, 1), (90676081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1218821, 1), (90676081, 1)] : List FactorBlock).map factorBlockValue).prod) = 663107470323007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_1218821
      · exact prime_oneHundredFortySixEN_90676081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 663107470323007) ^ 331553735161503 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 663107470323007) ^ 221035823441002 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 663107470323007) ^ 544056486 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 663107470323007) ^ 7312926 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_950355906561979 : Nat.Prime 950355906561979 := by
  apply lucas_primality 950355906561979 (10 : ZMod 950355906561979)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (22627521584809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (22627521584809, 1)] : List FactorBlock).map factorBlockValue).prod) = 950355906561979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_22627521584809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 950355906561979) ^ 475177953280989 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 950355906561979) ^ 316785302187326 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 950355906561979) ^ 135765129508854 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 950355906561979) ^ 42 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_993774131423389 : Nat.Prime 993774131423389 := by
  apply lucas_primality 993774131423389 (6 : ZMod 993774131423389)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (521, 1), (2069, 1), (3658381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (521, 1), (2069, 1), (3658381, 1)] : List FactorBlock).map factorBlockValue).prod) = 993774131423389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_521
      · exact prime_oneHundredFortySixEN_2069
      · exact prime_oneHundredFortySixEN_3658381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 993774131423389) ^ 496887065711694 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 993774131423389) ^ 331258043807796 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 993774131423389) ^ 141967733060484 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 993774131423389) ^ 1907435952828 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 993774131423389) ^ 480316158252 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 993774131423389) ^ 271643148 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1018064745893423 : Nat.Prime 1018064745893423 := by
  apply lucas_primality 1018064745893423 (5 : ZMod 1018064745893423)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (509032372946711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (509032372946711, 1)] : List FactorBlock).map factorBlockValue).prod) = 1018064745893423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_509032372946711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1018064745893423) ^ 509032372946711 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 1018064745893423) ^ 2 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1028954421588869 : Nat.Prime 1028954421588869 := by
  apply lucas_primality 1028954421588869 (2 : ZMod 1028954421588869)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257238605397217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257238605397217, 1)] : List FactorBlock).map factorBlockValue).prod) = 1028954421588869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_257238605397217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1028954421588869) ^ 514477210794434 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1028954421588869) ^ 4 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1170009366935947 : Nat.Prime 1170009366935947 := by
  apply lucas_primality 1170009366935947 (13 : ZMod 1170009366935947)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (127, 1), (313, 1), (2069, 1), (57829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (127, 1), (313, 1), (2069, 1), (57829, 1)] : List FactorBlock).map factorBlockValue).prod) = 1170009366935947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_41
      · exact prime_oneHundredFortySixEN_127
      · exact prime_oneHundredFortySixEN_313
      · exact prime_oneHundredFortySixEN_2069
      · exact prime_oneHundredFortySixEN_57829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1170009366935947) ^ 585004683467973 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 1170009366935947) ^ 390003122311982 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 1170009366935947) ^ 28536813827706 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 1170009366935947) ^ 9212672180598 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 1170009366935947) ^ 3738049095642 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 1170009366935947) ^ 565495102434 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 1170009366935947) ^ 20232225474 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1812499103657449 : Nat.Prime 1812499103657449 := by
  apply lucas_primality 1812499103657449 (19 : ZMod 1812499103657449)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (31, 1), (5867, 1), (138410017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (31, 1), (5867, 1), (138410017, 1)] : List FactorBlock).map factorBlockValue).prod) = 1812499103657449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_5867
      · exact prime_oneHundredFortySixEN_138410017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1812499103657449) ^ 906249551828724 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (19 : ZMod 1812499103657449) ^ 604166367885816 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (19 : ZMod 1812499103657449) ^ 58467713021208 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (19 : ZMod 1812499103657449) ^ 308931157944 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (19 : ZMod 1812499103657449) ^ 13095144 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1876163590812151 : Nat.Prime 1876163590812151 := by
  apply lucas_primality 1876163590812151 (6 : ZMod 1876163590812151)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (229, 1), (2777, 1), (2185373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (229, 1), (2777, 1), (2185373, 1)] : List FactorBlock).map factorBlockValue).prod) = 1876163590812151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_229
      · exact prime_oneHundredFortySixEN_2777
      · exact prime_oneHundredFortySixEN_2185373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1876163590812151) ^ 938081795406075 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 1876163590812151) ^ 625387863604050 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 1876163590812151) ^ 375232718162430 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 1876163590812151) ^ 8192854108350 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 1876163590812151) ^ 675608062950 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 1876163590812151) ^ 858509550 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_3770999619657583 : Nat.Prime 3770999619657583 := by
  apply lucas_primality 3770999619657583 (3 : ZMod 3770999619657583)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23209, 1), (2083077641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23209, 1), (2083077641, 1)] : List FactorBlock).map factorBlockValue).prod) = 3770999619657583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_23209
      · exact prime_oneHundredFortySixEN_2083077641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3770999619657583) ^ 1885499809828791 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 3770999619657583) ^ 1256999873219194 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 3770999619657583) ^ 290076893819814 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 3770999619657583) ^ 162480055998 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 3770999619657583) ^ 1810302 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_4774351500832681 : Nat.Prime 4774351500832681 := by
  apply lucas_primality 4774351500832681 (17 : ZMod 4774351500832681)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (13, 1), (59, 1), (17290857239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (13, 1), (59, 1), (17290857239, 1)] : List FactorBlock).map factorBlockValue).prod) = 4774351500832681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_59
      · exact prime_oneHundredFortySixEN_17290857239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 4774351500832681) ^ 2387175750416340 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 4774351500832681) ^ 1591450500277560 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 4774351500832681) ^ 954870300166536 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 4774351500832681) ^ 367257807756360 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 4774351500832681) ^ 80921211878520 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (17 : ZMod 4774351500832681) ^ 276120 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_7020056201615683 : Nat.Prime 7020056201615683 := by
  apply lucas_primality 7020056201615683 (3 : ZMod 7020056201615683)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1170009366935947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1170009366935947, 1)] : List FactorBlock).map factorBlockValue).prod) = 7020056201615683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_1170009366935947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7020056201615683) ^ 3510028100807841 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 7020056201615683) ^ 2340018733871894 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 7020056201615683) ^ 6 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_7764475661485513 : Nat.Prime 7764475661485513 := by
  apply lucas_primality 7764475661485513 (5 : ZMod 7764475661485513)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (214499, 1), (1508257937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (214499, 1), (1508257937, 1)] : List FactorBlock).map factorBlockValue).prod) = 7764475661485513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_214499
      · exact prime_oneHundredFortySixEN_1508257937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7764475661485513) ^ 3882237830742756 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 7764475661485513) ^ 2588158553828504 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 7764475661485513) ^ 36198190488 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 7764475661485513) ^ 5147976 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_18978431405382469 : Nat.Prime 18978431405382469 := by
  apply lucas_primality 18978431405382469 (2 : ZMod 18978431405382469)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79, 1), (6673147470247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79, 1), (6673147470247, 1)] : List FactorBlock).map factorBlockValue).prod) = 18978431405382469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_79
      · exact prime_oneHundredFortySixEN_6673147470247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18978431405382469) ^ 9489215702691234 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 18978431405382469) ^ 6326143801794156 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 18978431405382469) ^ 240233308928892 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 18978431405382469) ^ 2844 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_21355407518662883 : Nat.Prime 21355407518662883 := by
  apply lucas_primality 21355407518662883 (2 : ZMod 21355407518662883)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (217912321619009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (217912321619009, 1)] : List FactorBlock).map factorBlockValue).prod) = 21355407518662883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_217912321619009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21355407518662883) ^ 10677703759331441 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 21355407518662883) ^ 3050772502666126 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 21355407518662883) ^ 98 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_30369101218383757 : Nat.Prime 30369101218383757 := by
  apply lucas_primality 30369101218383757 (5 : ZMod 30369101218383757)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (71, 1), (32603, 1), (35267371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (71, 1), (32603, 1), (35267371, 1)] : List FactorBlock).map factorBlockValue).prod) = 30369101218383757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_71
      · exact prime_oneHundredFortySixEN_32603
      · exact prime_oneHundredFortySixEN_35267371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30369101218383757) ^ 15184550609191878 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 30369101218383757) ^ 10123033739461252 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 30369101218383757) ^ 979648426399476 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 30369101218383757) ^ 427733819977236 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 30369101218383757) ^ 931481802852 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 30369101218383757) ^ 861110436 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_34559348603190989 : Nat.Prime 34559348603190989 := by
  apply lucas_primality 34559348603190989 (2 : ZMod 34559348603190989)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4519, 1), (321311, 1), (5950283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4519, 1), (321311, 1), (5950283, 1)] : List FactorBlock).map factorBlockValue).prod) = 34559348603190989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_4519
      · exact prime_oneHundredFortySixEN_321311
      · exact prime_oneHundredFortySixEN_5950283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34559348603190989) ^ 17279674301595494 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 34559348603190989) ^ 7647565524052 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 34559348603190989) ^ 107557315508 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 34559348603190989) ^ 5808017636 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_47378215903540891 : Nat.Prime 47378215903540891 := by
  apply lucas_primality 47378215903540891 (3 : ZMod 47378215903540891)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (331, 1), (309109, 1), (15435397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (331, 1), (309109, 1), (15435397, 1)] : List FactorBlock).map factorBlockValue).prod) = 47378215903540891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_331
      · exact prime_oneHundredFortySixEN_309109
      · exact prime_oneHundredFortySixEN_15435397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47378215903540891) ^ 23689107951770445 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 47378215903540891) ^ 15792738634513630 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 47378215903540891) ^ 9475643180708178 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 47378215903540891) ^ 143136603938190 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 47378215903540891) ^ 153273492210 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 47378215903540891) ^ 3069452370 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_50332523929385591 : Nat.Prime 50332523929385591 := by
  apply lucas_primality 50332523929385591 (11 : ZMod 50332523929385591)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3808793, 1), (1321482263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3808793, 1), (1321482263, 1)] : List FactorBlock).map factorBlockValue).prod) = 50332523929385591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_3808793
      · exact prime_oneHundredFortySixEN_1321482263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 50332523929385591) ^ 25166261964692795 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 50332523929385591) ^ 10066504785877118 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 50332523929385591) ^ 13214822630 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 50332523929385591) ^ 38087930 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_88283490992487701 : Nat.Prime 88283490992487701 := by
  apply lucas_primality 88283490992487701 (2 : ZMod 88283490992487701)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (13, 1), (347, 1), (87509, 1), (319489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (13, 1), (347, 1), (87509, 1), (319489, 1)] : List FactorBlock).map factorBlockValue).prod) = 88283490992487701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_347
      · exact prime_oneHundredFortySixEN_87509
      · exact prime_oneHundredFortySixEN_319489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 88283490992487701) ^ 44141745496243850 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 88283490992487701) ^ 17656698198497540 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 88283490992487701) ^ 12611927284641100 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 88283490992487701) ^ 6791037768652900 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 88283490992487701) ^ 254419282399100 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 88283490992487701) ^ 1008850415300 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 88283490992487701) ^ 276327169300 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_131070729520427189 : Nat.Prime 131070729520427189 := by
  apply lucas_primality 131070729520427189 (2 : ZMod 131070729520427189)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (227, 1), (257, 1), (95467, 1), (255803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (227, 1), (257, 1), (95467, 1), (255803, 1)] : List FactorBlock).map factorBlockValue).prod) = 131070729520427189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_227
      · exact prime_oneHundredFortySixEN_257
      · exact prime_oneHundredFortySixEN_95467
      · exact prime_oneHundredFortySixEN_255803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 131070729520427189) ^ 65535364760213594 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 131070729520427189) ^ 5698727370453356 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 131070729520427189) ^ 577404094803644 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 131070729520427189) ^ 510002838600884 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 131070729520427189) ^ 1372942791964 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 131070729520427189) ^ 512389336796 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_131692216668598127 : Nat.Prime 131692216668598127 := by
  apply lucas_primality 131692216668598127 (5 : ZMod 131692216668598127)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18787, 1), (3504876155549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18787, 1), (3504876155549, 1)] : List FactorBlock).map factorBlockValue).prod) = 131692216668598127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_18787
      · exact prime_oneHundredFortySixEN_3504876155549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 131692216668598127) ^ 65846108334299063 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 131692216668598127) ^ 7009752311098 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 131692216668598127) ^ 37574 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_149623226369148353 : Nat.Prime 149623226369148353 := by
  apply lucas_primality 149623226369148353 (3 : ZMod 149623226369148353)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (19, 1), (647, 1), (15919, 1), (11946629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (19, 1), (647, 1), (15919, 1), (11946629, 1)] : List FactorBlock).map factorBlockValue).prod) = 149623226369148353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_647
      · exact prime_oneHundredFortySixEN_15919
      · exact prime_oneHundredFortySixEN_11946629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 149623226369148353) ^ 74811613184574176 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 149623226369148353) ^ 7874906651007808 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 149623226369148353) ^ 231256918654016 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 149623226369148353) ^ 9399034259008 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 149623226369148353) ^ 12524305088 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_171876654029976517 : Nat.Prime 171876654029976517 := by
  apply lucas_primality 171876654029976517 (2 : ZMod 171876654029976517)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4774351500832681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4774351500832681, 1)] : List FactorBlock).map factorBlockValue).prod) = 171876654029976517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_4774351500832681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 171876654029976517) ^ 85938327014988258 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 171876654029976517) ^ 57292218009992172 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 171876654029976517) ^ 36 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_186347415875652313 : Nat.Prime 186347415875652313 := by
  apply lucas_primality 186347415875652313 (5 : ZMod 186347415875652313)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7764475661485513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7764475661485513, 1)] : List FactorBlock).map factorBlockValue).prod) = 186347415875652313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7764475661485513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 186347415875652313) ^ 93173707937826156 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 186347415875652313) ^ 62115805291884104 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 186347415875652313) ^ 24 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_201470551492907387 : Nat.Prime 201470551492907387 := by
  apply lucas_primality 201470551492907387 (2 : ZMod 201470551492907387)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (7451, 1), (201786549229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (7451, 1), (201786549229, 1)] : List FactorBlock).map factorBlockValue).prod) = 201470551492907387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_67
      · exact prime_oneHundredFortySixEN_7451
      · exact prime_oneHundredFortySixEN_201786549229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 201470551492907387) ^ 100735275746453693 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 201470551492907387) ^ 3007023156610558 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 201470551492907387) ^ 27039397596686 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 201470551492907387) ^ 998434 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_215441737294357003 : Nat.Prime 215441737294357003 := by
  apply lucas_primality 215441737294357003 (2 : ZMod 215441737294357003)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (19, 1), (47, 1), (58991, 1), (4766563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (19, 1), (47, 1), (58991, 1), (4766563, 1)] : List FactorBlock).map factorBlockValue).prod) = 215441737294357003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_47
      · exact prime_oneHundredFortySixEN_58991
      · exact prime_oneHundredFortySixEN_4766563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 215441737294357003) ^ 107720868647178501 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 215441737294357003) ^ 71813912431452334 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 215441737294357003) ^ 19585612481305182 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 215441737294357003) ^ 16572441330335154 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 215441737294357003) ^ 11339038804966158 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 215441737294357003) ^ 4583866750943766 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 215441737294357003) ^ 3652111971222 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 215441737294357003) ^ 45198550254 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_242788875286020923 : Nat.Prime 242788875286020923 := by
  apply lucas_primality 242788875286020923 (2 : ZMod 242788875286020923)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (5689, 1), (257089749703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (5689, 1), (257089749703, 1)] : List FactorBlock).map factorBlockValue).prod) = 242788875286020923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_83
      · exact prime_oneHundredFortySixEN_5689
      · exact prime_oneHundredFortySixEN_257089749703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 242788875286020923) ^ 121394437643010461 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 242788875286020923) ^ 2925167172120734 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 242788875286020923) ^ 42676898450698 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 242788875286020923) ^ 944374 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_273998851665426253 : Nat.Prime 273998851665426253 := by
  apply lucas_primality 273998851665426253 (2 : ZMod 273998851665426253)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (74209, 1), (6033103019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (74209, 1), (6033103019, 1)] : List FactorBlock).map factorBlockValue).prod) = 273998851665426253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_17
      · exact prime_oneHundredFortySixEN_74209
      · exact prime_oneHundredFortySixEN_6033103019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 273998851665426253) ^ 136999425832713126 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 273998851665426253) ^ 91332950555142084 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 273998851665426253) ^ 16117579509730956 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 273998851665426253) ^ 3692259047628 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 273998851665426253) ^ 45415908 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_318920360358333703 : Nat.Prime 318920360358333703 := by
  apply lucas_primality 318920360358333703 (3 : ZMod 318920360358333703)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (467, 1), (55079, 1), (2066465069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (467, 1), (55079, 1), (2066465069, 1)] : List FactorBlock).map factorBlockValue).prod) = 318920360358333703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_467
      · exact prime_oneHundredFortySixEN_55079
      · exact prime_oneHundredFortySixEN_2066465069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 318920360358333703) ^ 159460180179166851 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 318920360358333703) ^ 106306786786111234 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 318920360358333703) ^ 682912977212706 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 318920360358333703) ^ 5790235123338 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 318920360358333703) ^ 154331358 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_391103134260984011 : Nat.Prime 391103134260984011 := by
  apply lucas_primality 391103134260984011 (2 : ZMod 391103134260984011)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (2339, 1), (576584650471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (2339, 1), (576584650471, 1)] : List FactorBlock).map factorBlockValue).prod) = 391103134260984011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_29
      · exact prime_oneHundredFortySixEN_2339
      · exact prime_oneHundredFortySixEN_576584650471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 391103134260984011) ^ 195551567130492005 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 391103134260984011) ^ 78220626852196802 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 391103134260984011) ^ 13486314974516690 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 391103134260984011) ^ 167209548636590 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 391103134260984011) ^ 678310 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_521960913783080833 : Nat.Prime 521960913783080833 := by
  apply lucas_primality 521960913783080833 (7 : ZMod 521960913783080833)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (71881, 1), (18910048733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (71881, 1), (18910048733, 1)] : List FactorBlock).map factorBlockValue).prod) = 521960913783080833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_71881
      · exact prime_oneHundredFortySixEN_18910048733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 521960913783080833) ^ 260980456891540416 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 521960913783080833) ^ 173986971261026944 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 521960913783080833) ^ 7261458713472 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 521960913783080833) ^ 27602304 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_530653607054093363 : Nat.Prime 530653607054093363 := by
  apply lucas_primality 530653607054093363 (2 : ZMod 530653607054093363)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (1031281, 1), (5250589049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (1031281, 1), (5250589049, 1)] : List FactorBlock).map factorBlockValue).prod) = 530653607054093363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_1031281
      · exact prime_oneHundredFortySixEN_5250589049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 530653607054093363) ^ 265326803527046681 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 530653607054093363) ^ 75807658150584766 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 530653607054093363) ^ 514557726802 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 530653607054093363) ^ 101065538 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1083023856458782361 : Nat.Prime 1083023856458782361 := by
  apply lucas_primality 1083023856458782361 (3 : ZMod 1083023856458782361)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (4217, 1), (5437, 1), (7639, 1), (154589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (4217, 1), (5437, 1), (7639, 1), (154589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1083023856458782361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_4217
      · exact prime_oneHundredFortySixEN_5437
      · exact prime_oneHundredFortySixEN_7639
      · exact prime_oneHundredFortySixEN_154589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1083023856458782361) ^ 541511928229391180 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1083023856458782361) ^ 216604771291756472 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1083023856458782361) ^ 256823300085080 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1083023856458782361) ^ 199195117980280 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1083023856458782361) ^ 141775606291240 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 1083023856458782361) ^ 7005827429240 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1093287643861815253 : Nat.Prime 1093287643861815253 := by
  apply lucas_primality 1093287643861815253 (2 : ZMod 1093287643861815253)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (30369101218383757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (30369101218383757, 1)] : List FactorBlock).map factorBlockValue).prod) = 1093287643861815253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_30369101218383757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1093287643861815253) ^ 546643821930907626 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1093287643861815253) ^ 364429214620605084 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1093287643861815253) ^ 36 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1520549922379694929 : Nat.Prime 1520549922379694929 := by
  apply lucas_primality 1520549922379694929 (11 : ZMod 1520549922379694929)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (53, 1), (229, 1), (617471, 1), (4226993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (53, 1), (229, 1), (617471, 1), (4226993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1520549922379694929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_53
      · exact prime_oneHundredFortySixEN_229
      · exact prime_oneHundredFortySixEN_617471
      · exact prime_oneHundredFortySixEN_4226993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1520549922379694929) ^ 760274961189847464 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 1520549922379694929) ^ 506849974126564976 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 1520549922379694929) ^ 28689621176975376 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 1520549922379694929) ^ 6639955992924432 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 1520549922379694929) ^ 2462544673968 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 1520549922379694929) ^ 359723785296 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1713620460877028423 : Nat.Prime 1713620460877028423 := by
  apply lucas_primality 1713620460877028423 (5 : ZMod 1713620460877028423)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3917, 1), (218741442542383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3917, 1), (218741442542383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1713620460877028423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3917
      · exact prime_oneHundredFortySixEN_218741442542383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1713620460877028423) ^ 856810230438514211 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 1713620460877028423) ^ 437482885084766 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 1713620460877028423) ^ 7834 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_101
      · exact prime_oneHundredFortySixEN_191
      · exact prime_oneHundredFortySixEN_48017
      · exact prime_oneHundredFortySixEN_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_3577188853191355121 : Nat.Prime 3577188853191355121 := by
  apply lucas_primality 3577188853191355121 (13 : ZMod 3577188853191355121)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (47, 1), (353, 1), (1051, 1), (6581, 1), (389659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (47, 1), (353, 1), (1051, 1), (6581, 1), (389659, 1)] : List FactorBlock).map factorBlockValue).prod) = 3577188853191355121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_47
      · exact prime_oneHundredFortySixEN_353
      · exact prime_oneHundredFortySixEN_1051
      · exact prime_oneHundredFortySixEN_6581
      · exact prime_oneHundredFortySixEN_389659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3577188853191355121) ^ 1788594426595677560 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 3577188853191355121) ^ 715437770638271024 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 3577188853191355121) ^ 76110401131730960 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 3577188853191355121) ^ 10133679470797040 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 3577188853191355121) ^ 3403604998279120 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 3577188853191355121) ^ 543563113993520 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 3577188853191355121) ^ 9180305993680 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_39281718014223477239 : Nat.Prime 39281718014223477239 := by
  apply lucas_primality 39281718014223477239 (13 : ZMod 39281718014223477239)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (110681, 1), (236129, 1), (32674597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (110681, 1), (236129, 1), (32674597, 1)] : List FactorBlock).map factorBlockValue).prod) = 39281718014223477239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_110681
      · exact prime_oneHundredFortySixEN_236129
      · exact prime_oneHundredFortySixEN_32674597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 39281718014223477239) ^ 19640859007111738619 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 39281718014223477239) ^ 1707900783227107706 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 39281718014223477239) ^ 354909316090598 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 39281718014223477239) ^ 166357025245622 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 39281718014223477239) ^ 1202209717054 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_39648440918849843243 : Nat.Prime 39648440918849843243 := by
  apply lucas_primality 39648440918849843243 (2 : ZMod 39648440918849843243)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (150067, 1), (132102463962263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (150067, 1), (132102463962263, 1)] : List FactorBlock).map factorBlockValue).prod) = 39648440918849843243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_150067
      · exact prime_oneHundredFortySixEN_132102463962263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39648440918849843243) ^ 19824220459424921621 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 39648440918849843243) ^ 264204927924526 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 39648440918849843243) ^ 300134 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_138268191523279544317 : Nat.Prime 138268191523279544317 := by
  apply lucas_primality 138268191523279544317 (2 : ZMod 138268191523279544317)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (31626869, 1), (121440509899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (31626869, 1), (121440509899, 1)] : List FactorBlock).map factorBlockValue).prod) = 138268191523279544317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_31626869
      · exact prime_oneHundredFortySixEN_121440509899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 138268191523279544317) ^ 69134095761639772158 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 138268191523279544317) ^ 46089397174426514772 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 138268191523279544317) ^ 4371858356364 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 138268191523279544317) ^ 1138567284 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_170845394105796657899 : Nat.Prime 170845394105796657899 := by
  apply lucas_primality 170845394105796657899 (2 : ZMod 170845394105796657899)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (71, 1), (171876654029976517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (71, 1), (171876654029976517, 1)] : List FactorBlock).map factorBlockValue).prod) = 170845394105796657899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_71
      · exact prime_oneHundredFortySixEN_171876654029976517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 170845394105796657899) ^ 85422697052898328949 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 170845394105796657899) ^ 24406484872256665414 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 170845394105796657899) ^ 2406273156419671238 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 170845394105796657899) ^ 994 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_221227453688028891527 : Nat.Prime 221227453688028891527 := by
  apply lucas_primality 221227453688028891527 (5 : ZMod 221227453688028891527)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (199293937, 1), (15000758327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (199293937, 1), (15000758327, 1)] : List FactorBlock).map factorBlockValue).prod) = 221227453688028891527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_37
      · exact prime_oneHundredFortySixEN_199293937
      · exact prime_oneHundredFortySixEN_15000758327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 221227453688028891527) ^ 110613726844014445763 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 221227453688028891527) ^ 5979120369946726798 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 221227453688028891527) ^ 1110056116198 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 221227453688028891527) ^ 14747751338 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_238208824118560447051 : Nat.Prime 238208824118560447051 := by
  apply lucas_primality 238208824118560447051 (23 : ZMod 238208824118560447051)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (61, 1), (67, 1), (21017, 1), (18488054993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (61, 1), (67, 1), (21017, 1), (18488054993, 1)] : List FactorBlock).map factorBlockValue).prod) = 238208824118560447051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_61
      · exact prime_oneHundredFortySixEN_67
      · exact prime_oneHundredFortySixEN_21017
      · exact prime_oneHundredFortySixEN_18488054993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 238208824118560447051) ^ 119104412059280223525 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 238208824118560447051) ^ 79402941372853482350 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 238208824118560447051) ^ 47641764823712089410 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 238208824118560447051) ^ 3905062690468204050 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 238208824118560447051) ^ 3555355583859111150 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 238208824118560447051) ^ 11334102113458650 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 238208824118560447051) ^ 12884471850 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_246394974584419926931 : Nat.Prime 246394974584419926931 := by
  apply lucas_primality 246394974584419926931 (7 : ZMod 246394974584419926931)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (391103134260984011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (391103134260984011, 1)] : List FactorBlock).map factorBlockValue).prod) = 246394974584419926931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_391103134260984011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 246394974584419926931) ^ 123197487292209963465 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 246394974584419926931) ^ 82131658194806642310 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 246394974584419926931) ^ 49278994916883985386 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 246394974584419926931) ^ 35199282083488560990 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 246394974584419926931) ^ 630 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_261857933529462490553 : Nat.Prime 261857933529462490553 := by
  apply lucas_primality 261857933529462490553 (3 : ZMod 261857933529462490553)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (4459597, 1), (109548221681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (4459597, 1), (109548221681, 1)] : List FactorBlock).map factorBlockValue).prod) = 261857933529462490553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_67
      · exact prime_oneHundredFortySixEN_4459597
      · exact prime_oneHundredFortySixEN_109548221681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 261857933529462490553) ^ 130928966764731245276 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 261857933529462490553) ^ 3908327366111380456 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 261857933529462490553) ^ 58717846821016 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 261857933529462490553) ^ 2390343992 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_326108258160227527973 : Nat.Prime 326108258160227527973 := by
  apply lucas_primality 326108258160227527973 (2 : ZMod 326108258160227527973)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (269, 1), (449, 1), (51923006573281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (269, 1), (449, 1), (51923006573281, 1)] : List FactorBlock).map factorBlockValue).prod) = 326108258160227527973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_269
      · exact prime_oneHundredFortySixEN_449
      · exact prime_oneHundredFortySixEN_51923006573281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 326108258160227527973) ^ 163054129080113763986 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 326108258160227527973) ^ 25085250627709809844 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 326108258160227527973) ^ 1212298357472964788 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 326108258160227527973) ^ 726299015947054628 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 326108258160227527973) ^ 6280612 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_341498215854440109449 : Nat.Prime 341498215854440109449 := by
  apply lucas_primality 341498215854440109449 (3 : ZMod 341498215854440109449)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (136193, 1), (1255357, 1), (249675781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (136193, 1), (1255357, 1), (249675781, 1)] : List FactorBlock).map factorBlockValue).prod) = 341498215854440109449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_136193
      · exact prime_oneHundredFortySixEN_1255357
      · exact prime_oneHundredFortySixEN_249675781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 341498215854440109449) ^ 170749107927220054724 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 341498215854440109449) ^ 2507457915270536 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 341498215854440109449) ^ 272032749133864 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 341498215854440109449) ^ 1367766687208 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_442974776847762544799 : Nat.Prime 442974776847762544799 := by
  apply lucas_primality 442974776847762544799 (7 : ZMod 442974776847762544799)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (108175621, 1), (7905327041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (108175621, 1), (7905327041, 1)] : List FactorBlock).map factorBlockValue).prod) = 442974776847762544799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_37
      · exact prime_oneHundredFortySixEN_108175621
      · exact prime_oneHundredFortySixEN_7905327041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 442974776847762544799) ^ 221487388423881272399 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 442974776847762544799) ^ 63282110978251792114 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 442974776847762544799) ^ 11972291266155744454 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 442974776847762544799) ^ 4094959407238 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 442974776847762544799) ^ 56034971678 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_485423649818265174691 : Nat.Prime 485423649818265174691 := by
  apply lucas_primality 485423649818265174691 (2 : ZMod 485423649818265174691)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (521960913783080833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (521960913783080833, 1)] : List FactorBlock).map factorBlockValue).prod) = 485423649818265174691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_521960913783080833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 485423649818265174691) ^ 242711824909132587345 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 485423649818265174691) ^ 161807883272755058230 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 485423649818265174691) ^ 97084729963653034938 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 485423649818265174691) ^ 15658827413492424990 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 485423649818265174691) ^ 930 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_583718967759502699301 : Nat.Prime 583718967759502699301 := by
  apply lucas_primality 583718967759502699301 (2 : ZMod 583718967759502699301)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (530653607054093363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (530653607054093363, 1)] : List FactorBlock).map factorBlockValue).prod) = 583718967759502699301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_530653607054093363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 583718967759502699301) ^ 291859483879751349650 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 583718967759502699301) ^ 116743793551900539860 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 583718967759502699301) ^ 53065360705409336300 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 583718967759502699301) ^ 1100 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_700752967983453774331 : Nat.Prime 700752967983453774331 := by
  apply lucas_primality 700752967983453774331 (2 : ZMod 700752967983453774331)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (59, 1), (13421, 1), (393727, 1), (24974129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (59, 1), (13421, 1), (393727, 1), (24974129, 1)] : List FactorBlock).map factorBlockValue).prod) = 700752967983453774331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_59
      · exact prime_oneHundredFortySixEN_13421
      · exact prime_oneHundredFortySixEN_393727
      · exact prime_oneHundredFortySixEN_24974129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 700752967983453774331) ^ 350376483991726887165 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 700752967983453774331) ^ 233584322661151258110 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 700752967983453774331) ^ 140150593596690754866 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 700752967983453774331) ^ 11877168948872097870 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 700752967983453774331) ^ 52213170999437730 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 700752967983453774331) ^ 1779794039990790 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 700752967983453774331) ^ 28059155455770 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1760345824576691762749 : Nat.Prime 1760345824576691762749 := by
  apply lucas_primality 1760345824576691762749 (2 : ZMod 1760345824576691762749)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (1070789, 1), (3512758070999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (1070789, 1), (3512758070999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1760345824576691762749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_1070789
      · exact prime_oneHundredFortySixEN_3512758070999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1760345824576691762749) ^ 880172912288345881374 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1760345824576691762749) ^ 586781941525563920916 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1760345824576691762749) ^ 135411217275130135596 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1760345824576691762749) ^ 1643970777227532 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1760345824576691762749) ^ 501129252 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2217950170618561326611 : Nat.Prime 2217950170618561326611 := by
  apply lucas_primality 2217950170618561326611 (2 : ZMod 2217950170618561326611)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (61, 1), (197, 1), (52757, 1), (26911151413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (61, 1), (197, 1), (52757, 1), (26911151413, 1)] : List FactorBlock).map factorBlockValue).prod) = 2217950170618561326611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_61
      · exact prime_oneHundredFortySixEN_197
      · exact prime_oneHundredFortySixEN_52757
      · exact prime_oneHundredFortySixEN_26911151413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2217950170618561326611) ^ 1108975085309280663305 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2217950170618561326611) ^ 443590034123712265322 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2217950170618561326611) ^ 170611551586043178970 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2217950170618561326611) ^ 36359838862599366010 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2217950170618561326611) ^ 11258630307708433130 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2217950170618561326611) ^ 42040869848902730 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2217950170618561326611) ^ 82417512970 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_16705781302212492209383 : Nat.Prime 16705781302212492209383 := by
  apply lucas_primality 16705781302212492209383 (5 : ZMod 16705781302212492209383)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (43, 1), (33023, 1), (150829818654721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (43, 1), (33023, 1), (150829818654721, 1)] : List FactorBlock).map factorBlockValue).prod) = 16705781302212492209383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_43
      · exact prime_oneHundredFortySixEN_33023
      · exact prime_oneHundredFortySixEN_150829818654721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16705781302212492209383) ^ 8352890651106246104691 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 16705781302212492209383) ^ 5568593767404164069794 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 16705781302212492209383) ^ 1285060100170191708414 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 16705781302212492209383) ^ 388506541911918423474 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 16705781302212492209383) ^ 505883211767934234 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 16705781302212492209383) ^ 110759142 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_17055349301601339680431 : Nat.Prime 17055349301601339680431 := by
  apply lucas_primality 17055349301601339680431 (39 : ZMod 17055349301601339680431)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (3159089, 1), (5597927, 1), (10715909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (3159089, 1), (5597927, 1), (10715909, 1)] : List FactorBlock).map factorBlockValue).prod) = 17055349301601339680431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_3159089
      · exact prime_oneHundredFortySixEN_5597927
      · exact prime_oneHundredFortySixEN_10715909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (39 : ZMod 17055349301601339680431) ^ 8527674650800669840215 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (39 : ZMod 17055349301601339680431) ^ 5685116433867113226810 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (39 : ZMod 17055349301601339680431) ^ 3411069860320267936086 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (39 : ZMod 17055349301601339680431) ^ 5398818868857870 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (39 : ZMod 17055349301601339680431) ^ 3046725922221090 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (39 : ZMod 17055349301601339680431) ^ 1591591464765270 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_29751642153401524686289 : Nat.Prime 29751642153401524686289 := by
  apply lucas_primality 29751642153401524686289 (13 : ZMod 29751642153401524686289)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (137, 1), (215441737294357003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (137, 1), (215441737294357003, 1)] : List FactorBlock).map factorBlockValue).prod) = 29751642153401524686289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_137
      · exact prime_oneHundredFortySixEN_215441737294357003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 29751642153401524686289) ^ 14875821076700762343144 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 29751642153401524686289) ^ 9917214051133841562096 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 29751642153401524686289) ^ 4250234593343074955184 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 29751642153401524686289) ^ 217165271192711859024 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (13 : ZMod 29751642153401524686289) ^ 138096 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_42794455390608992466983 : Nat.Prime 42794455390608992466983 := by
  apply lucas_primality 42794455390608992466983 (5 : ZMod 42794455390608992466983)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11968849817, 1), (1787743018123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11968849817, 1), (1787743018123, 1)] : List FactorBlock).map factorBlockValue).prod) = 42794455390608992466983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_11968849817
      · exact prime_oneHundredFortySixEN_1787743018123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 42794455390608992466983) ^ 21397227695304496233491 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 42794455390608992466983) ^ 3575486036246 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 42794455390608992466983) ^ 23937699634 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_77901963979179957638041 : Nat.Prime 77901963979179957638041 := by
  apply lucas_primality 77901963979179957638041 (7 : ZMod 77901963979179957638041)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (10133, 1), (21355407518662883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (10133, 1), (21355407518662883, 1)] : List FactorBlock).map factorBlockValue).prod) = 77901963979179957638041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_10133
      · exact prime_oneHundredFortySixEN_21355407518662883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 77901963979179957638041) ^ 38950981989589978819020 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 77901963979179957638041) ^ 25967321326393319212680 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 77901963979179957638041) ^ 15580392795835991527608 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 77901963979179957638041) ^ 7687946706718637880 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (7 : ZMod 77901963979179957638041) ^ 3647880 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_225442517219281913784371 : Nat.Prime 225442517219281913784371 := by
  apply lucas_primality 225442517219281913784371 (2 : ZMod 225442517219281913784371)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (541, 1), (63918103, 1), (651950589919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (541, 1), (63918103, 1), (651950589919, 1)] : List FactorBlock).map factorBlockValue).prod) = 225442517219281913784371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_541
      · exact prime_oneHundredFortySixEN_63918103
      · exact prime_oneHundredFortySixEN_651950589919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 225442517219281913784371) ^ 112721258609640956892185 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 225442517219281913784371) ^ 45088503443856382756874 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 225442517219281913784371) ^ 416714449573534036570 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 225442517219281913784371) ^ 3527052691461790 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 225442517219281913784371) ^ 345796937230 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_233741969968924956012527 : Nat.Prime 233741969968924956012527 := by
  apply lucas_primality 233741969968924956012527 (5 : ZMod 233741969968924956012527)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2861, 1), (401237, 1), (7831492197443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2861, 1), (401237, 1), (7831492197443, 1)] : List FactorBlock).map factorBlockValue).prod) = 233741969968924956012527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_2861
      · exact prime_oneHundredFortySixEN_401237
      · exact prime_oneHundredFortySixEN_7831492197443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 233741969968924956012527) ^ 116870984984462478006263 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 233741969968924956012527) ^ 17980151536071150462502 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 233741969968924956012527) ^ 81699395305461361766 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 233741969968924956012527) ^ 582553378598994998 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 233741969968924956012527) ^ 29846415482 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_243001775347462122310621 : Nat.Prime 243001775347462122310621 := by
  apply lucas_primality 243001775347462122310621 (2 : ZMod 243001775347462122310621)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (227, 2), (1274209, 1), (2937287917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (227, 2), (1274209, 1), (2937287917, 1)] : List FactorBlock).map factorBlockValue).prod) = 243001775347462122310621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_227
      · exact prime_oneHundredFortySixEN_1274209
      · exact prime_oneHundredFortySixEN_2937287917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 243001775347462122310621) ^ 121500887673731061155310 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 243001775347462122310621) ^ 81000591782487374103540 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 243001775347462122310621) ^ 48600355069492424462124 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 243001775347462122310621) ^ 34714539335351731758660 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 243001775347462122310621) ^ 1070492402411727411060 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 243001775347462122310621) ^ 190707941434617180 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 243001775347462122310621) ^ 82729981606860 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_379945950462712356520433 : Nat.Prime 379945950462712356520433 := by
  apply lucas_primality 379945950462712356520433 (3 : ZMod 379945950462712356520433)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (79, 2), (1009, 1), (3770999619657583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (79, 2), (1009, 1), (3770999619657583, 1)] : List FactorBlock).map factorBlockValue).prod) = 379945950462712356520433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_79
      · exact prime_oneHundredFortySixEN_1009
      · exact prime_oneHundredFortySixEN_3770999619657583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 379945950462712356520433) ^ 189972975231356178260216 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 379945950462712356520433) ^ 4809442410920409576208 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 379945950462712356520433) ^ 376556938020527608048 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 379945950462712356520433) ^ 100754704 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_702922134039517817971261 : Nat.Prime 702922134039517817971261 := by
  apply lucas_primality 702922134039517817971261 (6 : ZMod 702922134039517817971261)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 2), (23, 1), (273998851665426253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (13, 2), (23, 1), (273998851665426253, 1)] : List FactorBlock).map factorBlockValue).prod) = 702922134039517817971261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_273998851665426253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 702922134039517817971261) ^ 351461067019758908985630 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 702922134039517817971261) ^ 234307378013172605990420 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 702922134039517817971261) ^ 140584426807903563594252 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 702922134039517817971261) ^ 63902012185410710724660 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 702922134039517817971261) ^ 54070933387655216767020 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 702922134039517817971261) ^ 30561831914761644259620 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 702922134039517817971261) ^ 2565420 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_854822881050543636860329 : Nat.Prime 854822881050543636860329 := by
  apply lucas_primality 854822881050543636860329 (11 : ZMod 854822881050543636860329)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (23, 1), (221227453688028891527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (23, 1), (221227453688028891527, 1)] : List FactorBlock).map factorBlockValue).prod) = 854822881050543636860329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_221227453688028891527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 854822881050543636860329) ^ 427411440525271818430164 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 854822881050543636860329) ^ 284940960350181212286776 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 854822881050543636860329) ^ 122117554435791948122904 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 854822881050543636860329) ^ 37166212219588853776536 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 854822881050543636860329) ^ 3864 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1782876436529210816566051 : Nat.Prime 1782876436529210816566051 := by
  apply lucas_primality 1782876436529210816566051 (2 : ZMod 1782876436529210816566051)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (41, 1), (101, 1), (318920360358333703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (41, 1), (101, 1), (318920360358333703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1782876436529210816566051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_41
      · exact prime_oneHundredFortySixEN_101
      · exact prime_oneHundredFortySixEN_318920360358333703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1782876436529210816566051) ^ 891438218264605408283025 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1782876436529210816566051) ^ 594292145509736938855350 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1782876436529210816566051) ^ 356575287305842163313210 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1782876436529210816566051) ^ 43484791134858800404050 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1782876436529210816566051) ^ 17652241945833770461050 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 1782876436529210816566051) ^ 5590350 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_4869550739950124817802883 : Nat.Prime 4869550739950124817802883 := by
  apply lucas_primality 4869550739950124817802883 (2 : ZMod 4869550739950124817802883)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1097, 1), (18743953, 1), (118410737385001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1097, 1), (18743953, 1), (118410737385001, 1)] : List FactorBlock).map factorBlockValue).prod) = 4869550739950124817802883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_1097
      · exact prime_oneHundredFortySixEN_18743953
      · exact prime_oneHundredFortySixEN_118410737385001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4869550739950124817802883) ^ 2434775369975062408901441 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4869550739950124817802883) ^ 4438970592479603297906 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4869550739950124817802883) ^ 259793157822692194 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 4869550739950124817802883) ^ 41124232882 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_5526026542419390268173223 : Nat.Prime 5526026542419390268173223 := by
  apply lucas_primality 5526026542419390268173223 (11 : ZMod 5526026542419390268173223)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6661, 1), (138268191523279544317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6661, 1), (138268191523279544317, 1)] : List FactorBlock).map factorBlockValue).prod) = 5526026542419390268173223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_6661
      · exact prime_oneHundredFortySixEN_138268191523279544317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 5526026542419390268173223) ^ 2763013271209695134086611 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 5526026542419390268173223) ^ 1842008847473130089391074 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 5526026542419390268173223) ^ 829609149139677265902 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 5526026542419390268173223) ^ 39966 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_12047948982970061730764207 : Nat.Prime 12047948982970061730764207 := by
  apply lucas_primality 12047948982970061730764207 (10 : ZMod 12047948982970061730764207)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (761, 1), (22705061, 1), (1378019214431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (761, 1), (22705061, 1), (1378019214431, 1)] : List FactorBlock).map factorBlockValue).prod) = 12047948982970061730764207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_761
      · exact prime_oneHundredFortySixEN_22705061
      · exact prime_oneHundredFortySixEN_1378019214431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 12047948982970061730764207) ^ 6023974491485030865382103 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 12047948982970061730764207) ^ 1095268089360914702796746 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 12047948982970061730764207) ^ 523823868824785292641922 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 12047948982970061730764207) ^ 15831733223350935257246 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 12047948982970061730764207) ^ 530628346824087446 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (10 : ZMod 12047948982970061730764207) ^ 8742947019026 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_34126327615463043577828943 : Nat.Prime 34126327615463043577828943 := by
  apply lucas_primality 34126327615463043577828943 (5 : ZMod 34126327615463043577828943)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (233741969968924956012527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (233741969968924956012527, 1)] : List FactorBlock).map factorBlockValue).prod) = 34126327615463043577828943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_73
      · exact prime_oneHundredFortySixEN_233741969968924956012527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 34126327615463043577828943) ^ 17063163807731521788914471 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 34126327615463043577828943) ^ 467483939937849912025054 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 34126327615463043577828943) ^ 146 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_455437902583145315083532437 : Nat.Prime 455437902583145315083532437 := by
  apply lucas_primality 455437902583145315083532437 (2 : ZMod 455437902583145315083532437)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (11, 1), (417839, 1), (131070729520427189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (11, 1), (417839, 1), (131070729520427189, 1)] : List FactorBlock).map factorBlockValue).prod) = 455437902583145315083532437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_417839
      · exact prime_oneHundredFortySixEN_131070729520427189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 455437902583145315083532437) ^ 227718951291572657541766218 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 455437902583145315083532437) ^ 151812634194381771694510812 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 455437902583145315083532437) ^ 65062557511877902154790348 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 455437902583145315083532437) ^ 41403445689376846825775676 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 455437902583145315083532437) ^ 1089984186691872503724 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 455437902583145315083532437) ^ 3474749124 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_583145152293959710867090519 : Nat.Prime 583145152293959710867090519 := by
  apply lucas_primality 583145152293959710867090519 (11 : ZMod 583145152293959710867090519)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (31, 1), (53, 1), (769, 1), (1223, 1), (183375342907531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (31, 1), (53, 1), (769, 1), (1223, 1), (183375342907531, 1)] : List FactorBlock).map factorBlockValue).prod) = 583145152293959710867090519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_31
      · exact prime_oneHundredFortySixEN_53
      · exact prime_oneHundredFortySixEN_769
      · exact prime_oneHundredFortySixEN_1223
      · exact prime_oneHundredFortySixEN_183375342907531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 583145152293959710867090519) ^ 291572576146979855433545259 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 583145152293959710867090519) ^ 194381717431319903622363506 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 583145152293959710867090519) ^ 83306450327708530123870074 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 583145152293959710867090519) ^ 18811133944966442286035178 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 583145152293959710867090519) ^ 11002738722527541714473406 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 583145152293959710867090519) ^ 758316192839999624014422 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 583145152293959710867090519) ^ 476815333028585209212666 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (11 : ZMod 583145152293959710867090519) ^ 3180063050178 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_1207069685867217303612998557 : Nat.Prime 1207069685867217303612998557 := by
  apply lucas_primality 1207069685867217303612998557 (23 : ZMod 1207069685867217303612998557)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (28697, 1), (3907028003, 1), (69012017411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (28697, 1), (3907028003, 1), (69012017411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1207069685867217303612998557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_28697
      · exact prime_oneHundredFortySixEN_3907028003
      · exact prime_oneHundredFortySixEN_69012017411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1207069685867217303612998557) ^ 603534842933608651806499278 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 1207069685867217303612998557) ^ 402356561955739101204332852 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 1207069685867217303612998557) ^ 92851514297478254124076812 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 1207069685867217303612998557) ^ 42062573992654887396348 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 1207069685867217303612998557) ^ 308948306728380852 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (23 : ZMod 1207069685867217303612998557) ^ 17490717285926196 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2105011769256244809959253581 : Nat.Prime 2105011769256244809959253581 := by
  apply lucas_primality 2105011769256244809959253581 (2 : ZMod 2105011769256244809959253581)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (683, 1), (17032781713, 1), (695944963177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (683, 1), (17032781713, 1), (695944963177, 1)] : List FactorBlock).map factorBlockValue).prod) = 2105011769256244809959253581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_683
      · exact prime_oneHundredFortySixEN_17032781713
      · exact prime_oneHundredFortySixEN_695944963177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2105011769256244809959253581) ^ 1052505884628122404979626790 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2105011769256244809959253581) ^ 421002353851248961991850716 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2105011769256244809959253581) ^ 161923982250480369996865660 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2105011769256244809959253581) ^ 3082008446934472635372260 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2105011769256244809959253581) ^ 123585906560971660 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 2105011769256244809959253581) ^ 3024681376594540 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_2241700845181974992424140177 : Nat.Prime 2241700845181974992424140177 := by
  apply lucas_primality 2241700845181974992424140177 (3 : ZMod 2241700845181974992424140177)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (19, 1), (7933, 1), (333457, 1), (4312699, 1), (38021453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (19, 1), (7933, 1), (333457, 1), (4312699, 1), (38021453, 1)] : List FactorBlock).map factorBlockValue).prod) = 2241700845181974992424140177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_17
      · exact prime_oneHundredFortySixEN_19
      · exact prime_oneHundredFortySixEN_7933
      · exact prime_oneHundredFortySixEN_333457
      · exact prime_oneHundredFortySixEN_4312699
      · exact prime_oneHundredFortySixEN_38021453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2241700845181974992424140177) ^ 1120850422590987496212070088 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 2241700845181974992424140177) ^ 131864755598939705436714128 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 2241700845181974992424140177) ^ 117984255009577631180217904 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 2241700845181974992424140177) ^ 282579206502202822693072 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 2241700845181974992424140177) ^ 6722608447811786804368 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 2241700845181974992424140177) ^ 519790703033523784624 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 2241700845181974992424140177) ^ 58958842135306480592 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_3384528727039452439542329287 : Nat.Prime 3384528727039452439542329287 := by
  apply lucas_primality 3384528727039452439542329287 (3 : ZMod 3384528727039452439542329287)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (557, 1), (77901963979179957638041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (557, 1), (77901963979179957638041, 1)] : List FactorBlock).map factorBlockValue).prod) = 3384528727039452439542329287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_557
      · exact prime_oneHundredFortySixEN_77901963979179957638041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3384528727039452439542329287) ^ 1692264363519726219771164643 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 3384528727039452439542329287) ^ 1128176242346484146514109762 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 3384528727039452439542329287) ^ 260348363618419418426333022 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 3384528727039452439542329287) ^ 6076353190376036695767198 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 3384528727039452439542329287) ^ 43446 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_11507397671934138294443919577 : Nat.Prime 11507397671934138294443919577 := by
  apply lucas_primality 11507397671934138294443919577 (5 : ZMod 11507397671934138294443919577)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (866013149, 1), (50332523929385591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (866013149, 1), (50332523929385591, 1)] : List FactorBlock).map factorBlockValue).prod) = 11507397671934138294443919577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_11
      · exact prime_oneHundredFortySixEN_866013149
      · exact prime_oneHundredFortySixEN_50332523929385591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11507397671934138294443919577) ^ 5753698835967069147221959788 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 11507397671934138294443919577) ^ 3835799223978046098147973192 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 11507397671934138294443919577) ^ 1046127061084921663131265416 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 11507397671934138294443919577) ^ 13287786317357796024 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 11507397671934138294443919577) ^ 228627471336 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_19178996119890230490739865957 : Nat.Prime 19178996119890230490739865957 := by
  apply lucas_primality 19178996119890230490739865957 (2 : ZMod 19178996119890230490739865957)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (1928564951, 1), (18978431405382469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (1928564951, 1), (18978431405382469, 1)] : List FactorBlock).map factorBlockValue).prod) = 19178996119890230490739865957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_131
      · exact prime_oneHundredFortySixEN_1928564951
      · exact prime_oneHundredFortySixEN_18978431405382469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19178996119890230490739865957) ^ 9589498059945115245369932978 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 19178996119890230490739865957) ^ 146404550533513209852976076 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 19178996119890230490739865957) ^ 9944698056420413756 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 19178996119890230490739865957) ^ 1010568034324 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_19178996119890230490739865959 : Nat.Prime 19178996119890230490739865959 := by
  apply lucas_primality 19178996119890230490739865959 (3 : ZMod 19178996119890230490739865959)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (23, 1), (43, 1), (113, 1), (583718967759502699301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (23, 1), (43, 1), (113, 1), (583718967759502699301, 1)] : List FactorBlock).map factorBlockValue).prod) = 19178996119890230490739865959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_23
      · exact prime_oneHundredFortySixEN_43
      · exact prime_oneHundredFortySixEN_113
      · exact prime_oneHundredFortySixEN_583718967759502699301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19178996119890230490739865959) ^ 9589498059945115245369932979 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 19178996119890230490739865959) ^ 6392998706630076830246621986 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 19178996119890230490739865959) ^ 2739856588555747212962837994 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 19178996119890230490739865959) ^ 833869396516966543075646346 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 19178996119890230490739865959) ^ 446023165578842569552089906 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 19178996119890230490739865959) ^ 169725629379559561864954566 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 19178996119890230490739865959) ^ 32856558 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_57536988359670691472219597893 : Nat.Prime 57536988359670691472219597893 := by
  apply lucas_primality 57536988359670691472219597893 (2 : ZMod 57536988359670691472219597893)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (163, 1), (241, 1), (1801, 1), (14321, 1), (525813419822393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (163, 1), (241, 1), (1801, 1), (14321, 1), (525813419822393, 1)] : List FactorBlock).map factorBlockValue).prod) = 57536988359670691472219597893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_3
      · exact prime_oneHundredFortySixEN_163
      · exact prime_oneHundredFortySixEN_241
      · exact prime_oneHundredFortySixEN_1801
      · exact prime_oneHundredFortySixEN_14321
      · exact prime_oneHundredFortySixEN_525813419822393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57536988359670691472219597893) ^ 28768494179835345736109798946 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 57536988359670691472219597893) ^ 19178996119890230490739865964 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 57536988359670691472219597893) ^ 352987658648286450749813484 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 57536988359670691472219597893) ^ 238742690289090006108795012 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 57536988359670691472219597893) ^ 31947245063670567169472292 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 57536988359670691472219597893) ^ 4017665551265323055109252 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 57536988359670691472219597893) ^ 109424724038244 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_86305482539506037208329396801 : Nat.Prime 86305482539506037208329396801 := by
  apply lucas_primality 86305482539506037208329396801 (6 : ZMod 86305482539506037208329396801)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (73, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (73, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506037208329396801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_73
      · exact prime_oneHundredFortySixEN_171401
      · exact prime_oneHundredFortySixEN_714027719
      · exact prime_oneHundredFortySixEN_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 86305482539506037208329396801) ^ 43152741269753018604164698400 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 86305482539506037208329396801) ^ 17261096507901207441665879360 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 86305482539506037208329396801) ^ 1182266884102822427511361600 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 86305482539506037208329396801) ^ 503529632496345045876800 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 86305482539506037208329396801) ^ 120871333483211787200 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (6 : ZMod 86305482539506037208329396801) ^ 14294575599512459200 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_86305482539506037208329396807 : Nat.Prime 86305482539506037208329396807 := by
  apply lucas_primality 86305482539506037208329396807 (5 : ZMod 86305482539506037208329396807)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (47, 1), (109, 1), (661, 1), (719, 1), (48977309, 1), (27836550187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (47, 1), (109, 1), (661, 1), (719, 1), (48977309, 1), (27836550187, 1)] : List FactorBlock).map factorBlockValue).prod) = 86305482539506037208329396807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_13
      · exact prime_oneHundredFortySixEN_47
      · exact prime_oneHundredFortySixEN_109
      · exact prime_oneHundredFortySixEN_661
      · exact prime_oneHundredFortySixEN_719
      · exact prime_oneHundredFortySixEN_48977309
      · exact prime_oneHundredFortySixEN_27836550187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 86305482539506037208329396807) ^ 43152741269753018604164698403 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 86305482539506037208329396807) ^ 6638883272269695169871492062 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 86305482539506037208329396807) ^ 1836286862542681642730412698 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 86305482539506037208329396807) ^ 791793417793633368883755934 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 86305482539506037208329396807) ^ 130568052253413066880982446 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 86305482539506037208329396807) ^ 120035441640481275672224474 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 86305482539506037208329396807) ^ 1762152398767070628734 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (5 : ZMod 86305482539506037208329396807) ^ 3100437445003933138 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_172610965079012074416658793621 : Nat.Prime 172610965079012074416658793621 := by
  apply lucas_primality 172610965079012074416658793621 (3 : ZMod 172610965079012074416658793621)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (29, 1), (71, 1), (571, 1), (21407, 1), (90947, 1), (221795546653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (29, 1), (71, 1), (571, 1), (21407, 1), (90947, 1), (221795546653, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_5
      · exact prime_oneHundredFortySixEN_17
      · exact prime_oneHundredFortySixEN_29
      · exact prime_oneHundredFortySixEN_71
      · exact prime_oneHundredFortySixEN_571
      · exact prime_oneHundredFortySixEN_21407
      · exact prime_oneHundredFortySixEN_90947
      · exact prime_oneHundredFortySixEN_221795546653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 172610965079012074416658793621) ^ 86305482539506037208329396810 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 172610965079012074416658793621) ^ 34522193015802414883331758724 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 172610965079012074416658793621) ^ 10153586181118357318626987860 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 172610965079012074416658793621) ^ 5952102244103864635057199780 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 172610965079012074416658793621) ^ 2431140353225522174882518220 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 172610965079012074416658793621) ^ 302295910821387170607108220 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 172610965079012074416658793621) ^ 8063295421077781773095660 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 172610965079012074416658793621) ^ 1897929179401322467114460 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (3 : ZMod 172610965079012074416658793621) ^ 778243601748517540 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortySixEN_172610965079012074416658793693 : Nat.Prime 172610965079012074416658793693 := by
  apply lucas_primality 172610965079012074416658793693 (2 : ZMod 172610965079012074416658793693)
  · rw [← oneHundredFortySixENFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (107, 1), (82217, 1), (700752967983453774331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (107, 1), (82217, 1), (700752967983453774331, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortySixEN_2
      · exact prime_oneHundredFortySixEN_7
      · exact prime_oneHundredFortySixEN_107
      · exact prime_oneHundredFortySixEN_82217
      · exact prime_oneHundredFortySixEN_700752967983453774331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 172610965079012074416658793693) ^ 86305482539506037208329396846 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 172610965079012074416658793693) ^ 24658709297001724916665541956 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 172610965079012074416658793693) ^ 1613186589523477330996811156 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 172610965079012074416658793693) ^ 2099455892078427507895676 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide
    · change (2 : ZMod 172610965079012074416658793693) ^ 246322132 ≠ 1
      rw [← oneHundredFortySixENFastPow_eq_pow]
      decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793600 : Nat.totient 172610965079012074416658793600 = 68098175112098698832388096000 := by
  rw [← show ((([(2, 7), (5, 2), (73, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_73, prime_oneHundredFortySixEN_171401, prime_oneHundredFortySixEN_714027719, prime_oneHundredFortySixEN_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793601 : Nat.totient 172610965079012074416658793601 = 96226750417707900533587968000 := by
  rw [← show ((([(3, 1), (7, 1), (41, 1), (40801, 1), (179794273, 1), (27328674491317, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_41, prime_oneHundredFortySixEN_40801, prime_oneHundredFortySixEN_179794273, prime_oneHundredFortySixEN_27328674491317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793602 : Nat.totient 172610965079012074416658793602 = 86305482539506037208329396800 := by
  rw [← show ((([(2, 1), (86305482539506037208329396801, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_86305482539506037208329396801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793603 : Nat.totient 172610965079012074416658793603 = 161852853018803623946225865216 := by
  rw [← show ((([(17, 1), (269, 1), (320839, 1), (1785803, 1), (65878920945883, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_17, prime_oneHundredFortySixEN_269, prime_oneHundredFortySixEN_320839, prime_oneHundredFortySixEN_1785803, prime_oneHundredFortySixEN_65878920945883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793604 : Nat.totient 172610965079012074416658793604 = 57097774678463795841702696000 := by
  rw [← show ((([(2, 2), (3, 2), (131, 1), (1928564951, 1), (18978431405382469, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_131, prime_oneHundredFortySixEN_1928564951, prime_oneHundredFortySixEN_18978431405382469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793605 : Nat.totient 172610965079012074416658793605 = 138088765021826361226481539776 := by
  rw [← show ((([(5, 1), (19611029, 1), (1760345824576691762749, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_19611029, prime_oneHundredFortySixEN_1760345824576691762749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793606 : Nat.totient 172610965079012074416658793606 = 85822934210635409913266579880 := by
  rw [← show ((([(2, 1), (179, 1), (217387, 1), (2217950170618561326611, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_179, prime_oneHundredFortySixEN_217387, prime_oneHundredFortySixEN_2217950170618561326611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793607 : Nat.totient 172610965079012074416658793607 = 100018213333916811328019520000 := by
  rw [← show ((([(3, 1), (11, 1), (31, 1), (83, 1), (1159541, 1), (1494643, 1), (1172981257421, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_11, prime_oneHundredFortySixEN_31, prime_oneHundredFortySixEN_83, prime_oneHundredFortySixEN_1159541, prime_oneHundredFortySixEN_1494643, prime_oneHundredFortySixEN_1172981257421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793608 : Nat.totient 172610965079012074416658793608 = 73969106247403365634315201536 := by
  rw [← show ((([(2, 3), (7, 1), (10613, 1), (1441553, 1), (201470551492907387, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_10613, prime_oneHundredFortySixEN_1441553, prime_oneHundredFortySixEN_201470551492907387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793609 : Nat.totient 172610965079012074416658793609 = 163440342220764805867107351936 := by
  rw [← show ((([(19, 1), (2473, 1), (8293, 1), (442974776847762544799, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_19, prime_oneHundredFortySixEN_2473, prime_oneHundredFortySixEN_8293, prime_oneHundredFortySixEN_442974776847762544799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793610 : Nat.totient 172610965079012074416658793610 = 45249428133686424654433658432 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (59, 1), (2305632233699, 1), (42296563098107, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_59, prime_oneHundredFortySixEN_2305632233699, prime_oneHundredFortySixEN_42296563098107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793611 : Nat.totient 172610965079012074416658793611 = 172610965079010166683872134224 := by
  rw [← show ((([(95233683001939, 1), (1812499103657449, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_95233683001939, prime_oneHundredFortySixEN_1812499103657449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793612 : Nat.totient 172610965079012074416658793612 = 77032063399183031028366766080 := by
  rw [← show ((([(2, 2), (13, 1), (47, 1), (109, 1), (661, 1), (719, 1), (48977309, 1), (27836550187, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_13, prime_oneHundredFortySixEN_47, prime_oneHundredFortySixEN_109, prime_oneHundredFortySixEN_661, prime_oneHundredFortySixEN_719, prime_oneHundredFortySixEN_48977309, prime_oneHundredFortySixEN_27836550187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793613 : Nat.totient 172610965079012074416658793613 = 115073976719341382944439195736 := by
  rw [← show ((([(3, 2), (19178996119890230490739865957, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_19178996119890230490739865957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793614 : Nat.totient 172610965079012074416658793614 = 86305482539506037208329396806 := by
  rw [← show ((([(2, 1), (86305482539506037208329396807, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_86305482539506037208329396807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793615 : Nat.totient 172610965079012074416658793615 = 118361798908596500754046989600 := by
  rw [← show ((([(5, 1), (7, 1), (20703439, 1), (238208824118560447051, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_20703439, prime_oneHundredFortySixEN_238208824118560447051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793616 : Nat.totient 172610965079012074416658793616 = 57508462336686224099154508800 := by
  rw [← show ((([(2, 4), (3, 1), (2017, 1), (1782876436529210816566051, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_2017, prime_oneHundredFortySixEN_1782876436529210816566051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793617 : Nat.totient 172610965079012074416658793617 = 172521608472868172655885148800 := by
  rw [← show ((([(1987, 1), (69401, 1), (305069927, 1), (4103036564533, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_1987, prime_oneHundredFortySixEN_69401, prime_oneHundredFortySixEN_305069927, prime_oneHundredFortySixEN_4103036564533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793618 : Nat.totient 172610965079012074416658793618 = 78459529566882980305519562360 := by
  rw [← show ((([(2, 1), (11, 2), (5416177727, 1), (131692216668598127, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_11, prime_oneHundredFortySixEN_5416177727, prime_oneHundredFortySixEN_131692216668598127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793619 : Nat.totient 172610965079012074416658793619 = 114477738497632588083101462016 := by
  rw [← show ((([(3, 1), (193, 1), (313692069059, 1), (950355906561979, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_193, prime_oneHundredFortySixEN_313692069059, prime_oneHundredFortySixEN_950355906561979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793620 : Nat.totient 172610965079012074416658793620 = 61746570647595130427736883200 := by
  rw [← show ((([(2, 2), (5, 1), (17, 1), (29, 1), (71, 1), (571, 1), (21407, 1), (90947, 1), (221795546653, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_17, prime_oneHundredFortySixEN_29, prime_oneHundredFortySixEN_71, prime_oneHundredFortySixEN_571, prime_oneHundredFortySixEN_21407, prime_oneHundredFortySixEN_90947, prime_oneHundredFortySixEN_221795546653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793621 : Nat.totient 172610965079012074416658793621 = 172610965079012074416658793620 := by
  rw [← show ((([(172610965079012074416658793621, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_172610965079012074416658793621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793622 : Nat.totient 172610965079012074416658793622 = 45668378852834534000939750400 := by
  rw [← show ((([(2, 1), (3, 3), (7, 2), (23, 1), (43, 1), (113, 1), (583718967759502699301, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_23, prime_oneHundredFortySixEN_43, prime_oneHundredFortySixEN_113, prime_oneHundredFortySixEN_583718967759502699301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793623 : Nat.totient 172610965079012074416658793623 = 172155527176428929101575260808 := by
  rw [← show ((([(379, 1), (455437902583145315083532437, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_379, prime_oneHundredFortySixEN_455437902583145315083532437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793624 : Nat.totient 172610965079012074416658793624 = 83972901930330198364861034592 := by
  rw [← show ((([(2, 3), (37, 1), (583145152293959710867090519, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_37, prime_oneHundredFortySixEN_583145152293959710867090519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793625 : Nat.totient 172610965079012074416658793625 = 84357553516282524371644800000 := by
  rw [← show ((([(3, 1), (5, 3), (13, 1), (151, 1), (1471, 1), (9802017359, 1), (16262551069, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_13, prime_oneHundredFortySixEN_151, prime_oneHundredFortySixEN_1471, prime_oneHundredFortySixEN_9802017359, prime_oneHundredFortySixEN_16262551069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793626 : Nat.totient 172610965079012074416658793626 = 86305347232923936725326424160 := by
  rw [← show ((([(2, 1), (638171, 1), (1273359487, 1), (106206303084169, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_638171, prime_oneHundredFortySixEN_1273359487, prime_oneHundredFortySixEN_106206303084169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793627 : Nat.totient 172610965079012074416658793627 = 172610965079010106250981423400 := by
  rw [← show ((([(92002086558077, 1), (1876163590812151, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_92002086558077, prime_oneHundredFortySixEN_1876163590812151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793628 : Nat.totient 172610965079012074416658793628 = 54110851903370669505952189824 := by
  rw [← show ((([(2, 2), (3, 1), (19, 1), (137, 1), (5526026542419390268173223, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_19, prime_oneHundredFortySixEN_137, prime_oneHundredFortySixEN_5526026542419390268173223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793629 : Nat.totient 172610965079012074416658793629 = 134502050710918499545448410560 := by
  rw [← show ((([(7, 1), (11, 1), (2241700845181974992424140177, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_11, prime_oneHundredFortySixEN_2241700845181974992424140177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793630 : Nat.totient 172610965079012074416658793630 = 69044386031466590374401001632 := by
  rw [← show ((([(2, 1), (5, 1), (499462437967, 1), (34559348603190989, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_499462437967, prime_oneHundredFortySixEN_34559348603190989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793631 : Nat.totient 172610965079012074416658793631 = 115073976719341382944439195748 := by
  rw [← show ((([(3, 2), (19178996119890230490739865959, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_19178996119890230490739865959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793632 : Nat.totient 172610965079012074416658793632 = 86299403404298633810624842752 := by
  rw [← show ((([(2, 5), (14197, 1), (379945950462712356520433, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_14197, prime_oneHundredFortySixEN_379945950462712356520433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793633 : Nat.totient 172610965079012074416658793633 = 172610965039730356398041135748 := by
  rw [← show ((([(4394180647, 1), (39281718014223477239, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_4394180647, prime_oneHundredFortySixEN_39281718014223477239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793634 : Nat.totient 172610965079012074416658793634 = 57536537474636252908391773920 := by
  rw [← show ((([(2, 1), (3, 1), (127609, 1), (225442517219281913784371, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_127609, prime_oneHundredFortySixEN_225442517219281913784371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793635 : Nat.totient 172610965079012074416658793635 = 138088772062611165704940440064 := by
  rw [← show ((([(5, 1), (230727500359, 1), (149623226369148353, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_230727500359, prime_oneHundredFortySixEN_149623226369148353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793636 : Nat.totient 172610965079012074416658793636 = 73941350164020369338451517440 := by
  rw [← show ((([(2, 2), (7, 1), (2267, 1), (67993, 1), (69857, 1), (572512132654661, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_2267, prime_oneHundredFortySixEN_67993, prime_oneHundredFortySixEN_69857, prime_oneHundredFortySixEN_572512132654661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793637 : Nat.totient 172610965079012074416658793637 = 108304919265262478065354537152 := by
  rw [← show ((([(3, 1), (17, 1), (3384528727039452439542329287, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_17, prime_oneHundredFortySixEN_3384528727039452439542329287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793638 : Nat.totient 172610965079012074416658793638 = 76996637889351693978472128000 := by
  rw [← show ((([(2, 1), (13, 1), (31, 1), (881, 1), (6131, 1), (39648440918849843243, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_13, prime_oneHundredFortySixEN_31, prime_oneHundredFortySixEN_881, prime_oneHundredFortySixEN_6131, prime_oneHundredFortySixEN_39648440918849843243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793639 : Nat.totient 172610965079012074416658793639 = 172341658915707907750089456000 := by
  rw [← show ((([(647, 1), (70079, 1), (3579271, 1), (19239301, 1), (55283093, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_647, prime_oneHundredFortySixEN_70079, prime_oneHundredFortySixEN_3579271, prime_oneHundredFortySixEN_19239301, prime_oneHundredFortySixEN_55283093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793640 : Nat.totient 172610965079012074416658793640 = 41845082395077642721667827200 := by
  rw [← show ((([(2, 3), (3, 2), (5, 1), (11, 1), (866013149, 1), (50332523929385591, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_11, prime_oneHundredFortySixEN_866013149, prime_oneHundredFortySixEN_50332523929385591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793641 : Nat.totient 172610965079012074416658793641 = 172610965079011236224094615252 := by
  rw [← show ((([(364044228703567, 1), (474148335474823, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_364044228703567, prime_oneHundredFortySixEN_474148335474823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793642 : Nat.totient 172610965079012074416658793642 = 84200470770249792398370143200 := by
  rw [← show ((([(2, 1), (41, 1), (2105011769256244809959253581, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_41, prime_oneHundredFortySixEN_2105011769256244809959253581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793643 : Nat.totient 172610965079012074416658793643 = 97657775841668723220991328640 := by
  rw [← show ((([(3, 1), (7, 1), (181, 1), (227, 1), (28497323, 1), (7020056201615683, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_181, prime_oneHundredFortySixEN_227, prime_oneHundredFortySixEN_28497323, prime_oneHundredFortySixEN_7020056201615683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793644 : Nat.totient 172610965079012074416658793644 = 86118950120942941030795538880 := by
  rw [← show ((([(2, 2), (463, 1), (808399, 1), (4109071, 1), (28058082337093, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_463, prime_oneHundredFortySixEN_808399, prime_oneHundredFortySixEN_4109071, prime_oneHundredFortySixEN_28058082337093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793645 : Nat.totient 172610965079012074416658793645 = 132084584686575307374375760192 := by
  rw [← show ((([(5, 1), (23, 1), (461183, 1), (3196847, 1), (1018064745893423, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_23, prime_oneHundredFortySixEN_461183, prime_oneHundredFortySixEN_3196847, prime_oneHundredFortySixEN_1018064745893423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793646 : Nat.totient 172610965079012074416658793646 = 56451301485846100264148889600 := by
  rw [← show ((([(2, 1), (3, 1), (53, 1), (677561, 1), (19203765241, 1), (41716366297, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_53, prime_oneHundredFortySixEN_677561, prime_oneHundredFortySixEN_19203765241, prime_oneHundredFortySixEN_41716366297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793647 : Nat.totient 172610965079012074416658793647 = 163525876739211156990912457560 := by
  rw [← show ((([(19, 1), (543811, 1), (16705781302212492209383, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_19, prime_oneHundredFortySixEN_543811, prime_oneHundredFortySixEN_16705781302212492209383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793648 : Nat.totient 172610965079012074416658793648 = 86255894428149282713889196800 := by
  rw [← show ((([(2, 4), (1877, 1), (23911, 1), (2052258671, 1), (117126262919, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_1877, prime_oneHundredFortySixEN_23911, prime_oneHundredFortySixEN_2052258671, prime_oneHundredFortySixEN_117126262919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793649 : Nat.totient 172610965079012074416658793649 = 111105908010761449429919479680 := by
  rw [← show ((([(3, 3), (29, 1), (203548823, 1), (1083023856458782361, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_29, prime_oneHundredFortySixEN_203548823, prime_oneHundredFortySixEN_1083023856458782361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793650 : Nat.totient 172610965079012074416658793650 = 59180861452731936125728965120 := by
  rw [← show ((([(2, 1), (5, 2), (7, 1), (1493257, 1), (48194093, 1), (6852861675739, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_1493257, prime_oneHundredFortySixEN_48194093, prime_oneHundredFortySixEN_6852861675739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793651 : Nat.totient 172610965079012074416658793651 = 144848362304066076433559826720 := by
  rw [← show ((([(11, 1), (13, 1), (1207069685867217303612998557, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_11, prime_oneHundredFortySixEN_13, prime_oneHundredFortySixEN_1207069685867217303612998557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793652 : Nat.totient 172610965079012074416658793652 = 57536441708621973666168469504 := by
  rw [← show ((([(2, 2), (3, 1), (110039, 1), (4689809, 1), (5005709, 1), (5568263069, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_110039, prime_oneHundredFortySixEN_4689809, prime_oneHundredFortySixEN_5005709, prime_oneHundredFortySixEN_5568263069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793653 : Nat.totient 172610965079012074416658793653 = 169245832067212048389198397440 := by
  rw [← show ((([(61, 1), (353, 1), (3109, 1), (7244953, 1), (355883248261133, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_61, prime_oneHundredFortySixEN_353, prime_oneHundredFortySixEN_3109, prime_oneHundredFortySixEN_7244953, prime_oneHundredFortySixEN_355883248261133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793654 : Nat.totient 172610965079012074416658793654 = 81215012282850049850826042624 := by
  rw [← show ((([(2, 1), (17, 1), (5939, 1), (854822881050543636860329, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_17, prime_oneHundredFortySixEN_5939, prime_oneHundredFortySixEN_854822881050543636860329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793655 : Nat.totient 172610965079012074416658793655 = 92059181375473106355551356608 := by
  rw [← show ((([(3, 1), (5, 1), (11507397671934138294443919577, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_11507397671934138294443919577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793656 : Nat.totient 172610965079012074416658793656 = 85725728202986405500272683520 := by
  rw [← show ((([(2, 3), (149, 1), (164117, 1), (152625749, 1), (5781103537171, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_149, prime_oneHundredFortySixEN_164117, prime_oneHundredFortySixEN_152625749, prime_oneHundredFortySixEN_5781103537171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793657 : Nat.totient 172610965079012074416658793657 = 146047328164564554597550207488 := by
  rw [← show ((([(7, 1), (79, 1), (4937, 1), (57829, 1), (1093287643861815253, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_79, prime_oneHundredFortySixEN_4937, prime_oneHundredFortySixEN_57829, prime_oneHundredFortySixEN_1093287643861815253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793658 : Nat.totient 172610965079012074416658793658 = 56960434295359313977160388864 := by
  rw [← show ((([(2, 1), (3, 2), (103, 1), (3593, 1), (28547, 1), (640219, 1), (1417791603323, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_103, prime_oneHundredFortySixEN_3593, prime_oneHundredFortySixEN_28547, prime_oneHundredFortySixEN_640219, prime_oneHundredFortySixEN_1417791603323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793659 : Nat.totient 172610965079012074416658793659 = 166976685076294054684834598400 := by
  rw [← show ((([(47, 1), (101, 1), (587, 1), (40739, 1), (1520549922379694929, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_47, prime_oneHundredFortySixEN_101, prime_oneHundredFortySixEN_587, prime_oneHundredFortySixEN_40739, prime_oneHundredFortySixEN_1520549922379694929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793660 : Nat.totient 172610965079012074416658793660 = 67799274513792898283051581440 := by
  rw [← show ((([(2, 2), (5, 1), (67, 1), (317, 1), (1691423, 1), (19941931, 1), (12047165569, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_67, prime_oneHundredFortySixEN_317, prime_oneHundredFortySixEN_1691423, prime_oneHundredFortySixEN_19941931, prime_oneHundredFortySixEN_12047165569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793661 : Nat.totient 172610965079012074416658793661 = 111963869117059591237997721024 := by
  rw [← show ((([(3, 1), (37, 1), (907466837, 1), (1713620460877028423, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_37, prime_oneHundredFortySixEN_907466837, prime_oneHundredFortySixEN_1713620460877028423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793662 : Nat.totient 172610965079012074416658793662 = 78429866090378906419523373600 := by
  rw [← show ((([(2, 1), (11, 1), (3923, 1), (8117, 1), (246394974584419926931, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_11, prime_oneHundredFortySixEN_3923, prime_oneHundredFortySixEN_8117, prime_oneHundredFortySixEN_246394974584419926931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793663 : Nat.totient 172610965079012074416658793663 = 172610965078923788970476687400 := by
  rw [← show ((([(1955189618563, 1), (88283490992487701, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_1955189618563, prime_oneHundredFortySixEN_88283490992487701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793664 : Nat.totient 172610965079012074416658793664 = 45523754526163102789199708160 := by
  rw [← show ((([(2, 6), (3, 1), (7, 1), (13, 1), (2761747, 1), (3577188853191355121, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_13, prime_oneHundredFortySixEN_2761747, prime_oneHundredFortySixEN_3577188853191355121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793665 : Nat.totient 172610965079012074416658793665 = 134823518539985119640659911936 := by
  rw [← show ((([(5, 1), (43, 1), (2503, 1), (311725933, 1), (1028954421588869, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_43, prime_oneHundredFortySixEN_2503, prime_oneHundredFortySixEN_311725933, prime_oneHundredFortySixEN_1028954421588869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793666 : Nat.totient 172610965079012074416658793666 = 80915352190210452602644070400 := by
  rw [← show ((([(2, 1), (19, 1), (97, 1), (41081, 1), (45281, 1), (76243, 1), (330184024897, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_19, prime_oneHundredFortySixEN_97, prime_oneHundredFortySixEN_41081, prime_oneHundredFortySixEN_45281, prime_oneHundredFortySixEN_76243, prime_oneHundredFortySixEN_330184024897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793667 : Nat.totient 172610965079012074416658793667 = 114964277980755174637404386688 := by
  rw [← show ((([(3, 2), (1049, 1), (3485318574149, 1), (5245753781063, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_1049, prime_oneHundredFortySixEN_3485318574149, prime_oneHundredFortySixEN_5245753781063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793668 : Nat.totient 172610965079012074416658793668 = 82553055906416328714224611296 := by
  rw [← show ((([(2, 2), (23, 1), (5753323, 1), (326108258160227527973, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_23, prime_oneHundredFortySixEN_5753323, prime_oneHundredFortySixEN_326108258160227527973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793669 : Nat.totient 172610965079012074416658793669 = 164143181554202698263516165120 := by
  rw [← show ((([(31, 1), (59, 1), (2399, 1), (59325377, 1), (663107470323007, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_31, prime_oneHundredFortySixEN_59, prime_oneHundredFortySixEN_2399, prime_oneHundredFortySixEN_59325377, prime_oneHundredFortySixEN_663107470323007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793670 : Nat.totient 172610965079012074416658793670 = 45987571998593380939332648960 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1193, 1), (13921, 1), (348617, 1), (993774131423389, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_1193, prime_oneHundredFortySixEN_13921, prime_oneHundredFortySixEN_348617, prime_oneHundredFortySixEN_993774131423389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793671 : Nat.totient 172610965079012074416658793671 = 139175073657200841084019012608 := by
  rw [← show ((([(7, 3), (17, 1), (1879, 1), (1138292633, 1), (13840272280063, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_17, prime_oneHundredFortySixEN_1879, prime_oneHundredFortySixEN_1138292633, prime_oneHundredFortySixEN_13840272280063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793672 : Nat.totient 172610965079012074416658793672 = 86305224456081659081065297920 := by
  rw [← show ((([(2, 3), (334721, 1), (359041283, 1), (179535793808563, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_334721, prime_oneHundredFortySixEN_359041283, prime_oneHundredFortySixEN_179535793808563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793673 : Nat.totient 172610965079012074416658793673 = 102954367439372969034610176000 := by
  rw [← show ((([(3, 1), (11, 1), (73, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_11, prime_oneHundredFortySixEN_73, prime_oneHundredFortySixEN_461, prime_oneHundredFortySixEN_69997, prime_oneHundredFortySixEN_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793674 : Nat.totient 172610965079012074416658793674 = 85934993515613066114417301760 := by
  rw [← show ((([(2, 1), (233, 1), (1084661, 1), (341498215854440109449, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_233, prime_oneHundredFortySixEN_1084661, prime_oneHundredFortySixEN_341498215854440109449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793675 : Nat.totient 172610965079012074416658793675 = 138088772058353881458845910720 := by
  rw [← show ((([(5, 2), (28438035289, 1), (242788875286020923, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_28438035289, prime_oneHundredFortySixEN_242788875286020923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793676 : Nat.totient 172610965079012074416658793676 = 56911128947195331709255680000 := by
  rw [← show ((([(2, 2), (3, 4), (163, 1), (241, 1), (1801, 1), (14321, 1), (525813419822393, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_163, prime_oneHundredFortySixEN_241, prime_oneHundredFortySixEN_1801, prime_oneHundredFortySixEN_14321, prime_oneHundredFortySixEN_525813419822393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793677 : Nat.totient 172610965079012074416658793677 = 158890835642770958383918070784 := by
  rw [← show ((([(13, 2), (373, 1), (10457, 1), (261857933529462490553, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_13, prime_oneHundredFortySixEN_373, prime_oneHundredFortySixEN_10457, prime_oneHundredFortySixEN_261857933529462490553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793678 : Nat.totient 172610965079012074416658793678 = 71425005122399763970109474304 := by
  rw [← show ((([(2, 1), (7, 1), (29, 1), (333029, 1), (9737093, 1), (131108538381629, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_29, prime_oneHundredFortySixEN_333029, prime_oneHundredFortySixEN_9737093, prime_oneHundredFortySixEN_131108538381629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793679 : Nat.totient 172610965079012074416658793679 = 115073976719341382944439195784 := by
  rw [← show ((([(3, 1), (57536988359670691472219597893, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_57536988359670691472219597893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793680 : Nat.totient 172610965079012074416658793680 = 68807143283533756295235905024 := by
  rw [← show ((([(2, 4), (5, 1), (293, 1), (43103, 1), (170845394105796657899, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_293, prime_oneHundredFortySixEN_43103, prime_oneHundredFortySixEN_170845394105796657899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793681 : Nat.totient 172610965079012074416658793681 = 172610935327369921015128305664 := by
  rw [← show ((([(5801729, 1), (29751642153401524686289, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_5801729, prime_oneHundredFortySixEN_29751642153401524686289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793682 : Nat.totient 172610965079012074416658793682 = 57535582515402612436583573520 := by
  rw [← show ((([(2, 1), (3, 1), (40927, 1), (702922134039517817971261, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_40927, prime_oneHundredFortySixEN_702922134039517817971261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793683 : Nat.totient 172610965079012074416658793683 = 168362582407804872314632028160 := by
  rw [← show ((([(41, 1), (4409, 1), (1300193, 1), (4834463, 1), (151910698573, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_41, prime_oneHundredFortySixEN_4409, prime_oneHundredFortySixEN_1300193, prime_oneHundredFortySixEN_4834463, prime_oneHundredFortySixEN_151910698573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793684 : Nat.totient 172610965079012074416658793684 = 78459519154343235662187084000 := by
  rw [← show ((([(2, 2), (11, 1), (7553603, 1), (1976634587, 1), (262745422351, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_11, prime_oneHundredFortySixEN_7553603, prime_oneHundredFortySixEN_1976634587, prime_oneHundredFortySixEN_262745422351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793685 : Nat.totient 172610965079012074416658793685 = 73914882131663124339199864320 := by
  rw [← show ((([(3, 2), (5, 1), (7, 1), (19, 2), (89, 1), (17055349301601339680431, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_19, prime_oneHundredFortySixEN_89, prime_oneHundredFortySixEN_17055349301601339680431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793686 : Nat.totient 172610965079012074416658793686 = 86303837121228202865194828224 := by
  rw [← show ((([(2, 1), (52453, 1), (2756301673, 1), (596954601285047, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_52453, prime_oneHundredFortySixEN_2756301673, prime_oneHundredFortySixEN_596954601285047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793687 : Nat.totient 172610965079012074416658793687 = 172610922284556683807662293216 := by
  rw [← show ((([(4033489, 1), (42794455390608992466983, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_4033489, prime_oneHundredFortySixEN_42794455390608992466983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793688 : Nat.totient 172610965079012074416658793688 = 54121355405386763881021286400 := by
  rw [← show ((([(2, 3), (3, 1), (17, 1), (1741, 1), (243001775347462122310621, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_17, prime_oneHundredFortySixEN_1741, prime_oneHundredFortySixEN_243001775347462122310621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793689 : Nat.totient 172610965079012074416658793689 = 172598917130029104354928015156 := by
  rw [← show ((([(14327, 1), (12047948982970061730764207, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_14327, prime_oneHundredFortySixEN_12047948982970061730764207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793690 : Nat.totient 172610965079012074416658793690 = 62956092301106926890881922048 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (83, 1), (8893, 1), (31139, 1), (294059, 1), (196453380427, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_13, prime_oneHundredFortySixEN_83, prime_oneHundredFortySixEN_8893, prime_oneHundredFortySixEN_31139, prime_oneHundredFortySixEN_294059, prime_oneHundredFortySixEN_196453380427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793691 : Nat.totient 172610965079012074416658793691 = 108166981059490635130568227200 := by
  rw [← show ((([(3, 1), (23, 1), (71, 1), (307, 1), (7057559941, 1), (16261776595607, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_23, prime_oneHundredFortySixEN_71, prime_oneHundredFortySixEN_307, prime_oneHundredFortySixEN_7057559941, prime_oneHundredFortySixEN_16261776595607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793692 : Nat.totient 172610965079012074416658793692 = 73283870852005552369121036160 := by
  rw [← show ((([(2, 2), (7, 1), (107, 1), (82217, 1), (700752967983453774331, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_107, prime_oneHundredFortySixEN_82217, prime_oneHundredFortySixEN_700752967983453774331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793693 : Nat.totient 172610965079012074416658793693 = 172610965079012074416658793692 := by
  rw [← show ((([(172610965079012074416658793693, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_172610965079012074416658793693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793694 : Nat.totient 172610965079012074416658793694 = 57332230393977913210752622560 := by
  rw [← show ((([(2, 1), (3, 2), (281, 1), (34126327615463043577828943, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_281, prime_oneHundredFortySixEN_34126327615463043577828943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793695 : Nat.totient 172610965079012074416658793695 = 125288758297785136353091200000 := by
  rw [← show ((([(5, 1), (11, 1), (941, 1), (1129, 1), (62351, 1), (47378215903540891, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_11, prime_oneHundredFortySixEN_941, prime_oneHundredFortySixEN_1129, prime_oneHundredFortySixEN_62351, prime_oneHundredFortySixEN_47378215903540891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793696 : Nat.totient 172610965079012074416658793696 = 86133899566541910450346358784 := by
  rw [← show ((([(2, 5), (503, 1), (57547577, 1), (186347415875652313, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_503, prime_oneHundredFortySixEN_57547577, prime_oneHundredFortySixEN_186347415875652313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793697 : Nat.totient 172610965079012074416658793697 = 114726268761835877319891643200 := by
  rw [← show ((([(3, 1), (331, 1), (3017087, 1), (7959821, 1), (7238156970427, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_331, prime_oneHundredFortySixEN_3017087, prime_oneHundredFortySixEN_7959821, prime_oneHundredFortySixEN_7238156970427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793698 : Nat.totient 172610965079012074416658793698 = 83956177571954041173124336320 := by
  rw [← show ((([(2, 1), (37, 1), (5021, 1), (4154264579, 1), (111828445255403, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_37, prime_oneHundredFortySixEN_5021, prime_oneHundredFortySixEN_4154264579, prime_oneHundredFortySixEN_111828445255403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793699 : Nat.totient 172610965079012074416658793699 = 145160552333944618474544742240 := by
  rw [← show ((([(7, 1), (53, 1), (958459, 1), (485423649818265174691, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_7, prime_oneHundredFortySixEN_53, prime_oneHundredFortySixEN_958459, prime_oneHundredFortySixEN_485423649818265174691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793700 : Nat.totient 172610965079012074416658793700 = 44513185686347828303246131200 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (31, 1), (1553, 1), (16453, 1), (233297, 1), (3113577818033, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_2, prime_oneHundredFortySixEN_3, prime_oneHundredFortySixEN_5, prime_oneHundredFortySixEN_31, prime_oneHundredFortySixEN_1553, prime_oneHundredFortySixEN_16453, prime_oneHundredFortySixEN_233297, prime_oneHundredFortySixEN_3113577818033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortySixEN_172610965079012074416658793701 : Nat.totient 172610965079012074416658793701 = 172606095528272124291840955372 := by
  rw [← show ((([(35447, 1), (4869550739950124817802883, 1)] : List FactorBlock).map factorBlockValue).prod) = 172610965079012074416658793701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortySixEN_35447, prime_oneHundredFortySixEN_4869550739950124817802883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFortySixEN : certifiedKill 1 172610965079012074416658793599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFortySixEN_172610965079012074416658793600, phi_oneHundredFortySixEN_172610965079012074416658793601, phi_oneHundredFortySixEN_172610965079012074416658793602,
    phi_oneHundredFortySixEN_172610965079012074416658793603, phi_oneHundredFortySixEN_172610965079012074416658793604, phi_oneHundredFortySixEN_172610965079012074416658793605,
    phi_oneHundredFortySixEN_172610965079012074416658793606, phi_oneHundredFortySixEN_172610965079012074416658793607, phi_oneHundredFortySixEN_172610965079012074416658793608,
    phi_oneHundredFortySixEN_172610965079012074416658793609, phi_oneHundredFortySixEN_172610965079012074416658793610, phi_oneHundredFortySixEN_172610965079012074416658793611,
    phi_oneHundredFortySixEN_172610965079012074416658793612, phi_oneHundredFortySixEN_172610965079012074416658793613, phi_oneHundredFortySixEN_172610965079012074416658793614,
    phi_oneHundredFortySixEN_172610965079012074416658793615, phi_oneHundredFortySixEN_172610965079012074416658793616, phi_oneHundredFortySixEN_172610965079012074416658793617,
    phi_oneHundredFortySixEN_172610965079012074416658793618, phi_oneHundredFortySixEN_172610965079012074416658793619, phi_oneHundredFortySixEN_172610965079012074416658793620,
    phi_oneHundredFortySixEN_172610965079012074416658793621, phi_oneHundredFortySixEN_172610965079012074416658793622, phi_oneHundredFortySixEN_172610965079012074416658793623,
    phi_oneHundredFortySixEN_172610965079012074416658793624, phi_oneHundredFortySixEN_172610965079012074416658793625, phi_oneHundredFortySixEN_172610965079012074416658793626,
    phi_oneHundredFortySixEN_172610965079012074416658793627, phi_oneHundredFortySixEN_172610965079012074416658793628, phi_oneHundredFortySixEN_172610965079012074416658793629,
    phi_oneHundredFortySixEN_172610965079012074416658793630, phi_oneHundredFortySixEN_172610965079012074416658793631, phi_oneHundredFortySixEN_172610965079012074416658793632,
    phi_oneHundredFortySixEN_172610965079012074416658793633, phi_oneHundredFortySixEN_172610965079012074416658793634, phi_oneHundredFortySixEN_172610965079012074416658793635,
    phi_oneHundredFortySixEN_172610965079012074416658793636, phi_oneHundredFortySixEN_172610965079012074416658793637, phi_oneHundredFortySixEN_172610965079012074416658793638,
    phi_oneHundredFortySixEN_172610965079012074416658793639, phi_oneHundredFortySixEN_172610965079012074416658793640, phi_oneHundredFortySixEN_172610965079012074416658793641,
    phi_oneHundredFortySixEN_172610965079012074416658793642, phi_oneHundredFortySixEN_172610965079012074416658793643, phi_oneHundredFortySixEN_172610965079012074416658793644,
    phi_oneHundredFortySixEN_172610965079012074416658793645, phi_oneHundredFortySixEN_172610965079012074416658793646, phi_oneHundredFortySixEN_172610965079012074416658793647,
    phi_oneHundredFortySixEN_172610965079012074416658793648, phi_oneHundredFortySixEN_172610965079012074416658793649, phi_oneHundredFortySixEN_172610965079012074416658793650,
    phi_oneHundredFortySixEN_172610965079012074416658793651, phi_oneHundredFortySixEN_172610965079012074416658793652, phi_oneHundredFortySixEN_172610965079012074416658793653,
    phi_oneHundredFortySixEN_172610965079012074416658793654, phi_oneHundredFortySixEN_172610965079012074416658793655, phi_oneHundredFortySixEN_172610965079012074416658793656,
    phi_oneHundredFortySixEN_172610965079012074416658793657, phi_oneHundredFortySixEN_172610965079012074416658793658, phi_oneHundredFortySixEN_172610965079012074416658793659,
    phi_oneHundredFortySixEN_172610965079012074416658793660, phi_oneHundredFortySixEN_172610965079012074416658793661, phi_oneHundredFortySixEN_172610965079012074416658793662,
    phi_oneHundredFortySixEN_172610965079012074416658793663, phi_oneHundredFortySixEN_172610965079012074416658793664, phi_oneHundredFortySixEN_172610965079012074416658793665,
    phi_oneHundredFortySixEN_172610965079012074416658793666, phi_oneHundredFortySixEN_172610965079012074416658793667, phi_oneHundredFortySixEN_172610965079012074416658793668,
    phi_oneHundredFortySixEN_172610965079012074416658793669, phi_oneHundredFortySixEN_172610965079012074416658793670, phi_oneHundredFortySixEN_172610965079012074416658793671,
    phi_oneHundredFortySixEN_172610965079012074416658793672, phi_oneHundredFortySixEN_172610965079012074416658793673, phi_oneHundredFortySixEN_172610965079012074416658793674,
    phi_oneHundredFortySixEN_172610965079012074416658793675, phi_oneHundredFortySixEN_172610965079012074416658793676, phi_oneHundredFortySixEN_172610965079012074416658793677,
    phi_oneHundredFortySixEN_172610965079012074416658793678, phi_oneHundredFortySixEN_172610965079012074416658793679, phi_oneHundredFortySixEN_172610965079012074416658793680,
    phi_oneHundredFortySixEN_172610965079012074416658793681, phi_oneHundredFortySixEN_172610965079012074416658793682, phi_oneHundredFortySixEN_172610965079012074416658793683,
    phi_oneHundredFortySixEN_172610965079012074416658793684, phi_oneHundredFortySixEN_172610965079012074416658793685, phi_oneHundredFortySixEN_172610965079012074416658793686,
    phi_oneHundredFortySixEN_172610965079012074416658793687, phi_oneHundredFortySixEN_172610965079012074416658793688, phi_oneHundredFortySixEN_172610965079012074416658793689,
    phi_oneHundredFortySixEN_172610965079012074416658793690, phi_oneHundredFortySixEN_172610965079012074416658793691, phi_oneHundredFortySixEN_172610965079012074416658793692,
    phi_oneHundredFortySixEN_172610965079012074416658793693, phi_oneHundredFortySixEN_172610965079012074416658793694, phi_oneHundredFortySixEN_172610965079012074416658793695,
    phi_oneHundredFortySixEN_172610965079012074416658793696, phi_oneHundredFortySixEN_172610965079012074416658793697, phi_oneHundredFortySixEN_172610965079012074416658793698,
    phi_oneHundredFortySixEN_172610965079012074416658793699, phi_oneHundredFortySixEN_172610965079012074416658793700, phi_oneHundredFortySixEN_172610965079012074416658793701]

end TotientTailPeriodKiller
end Erdos249257
