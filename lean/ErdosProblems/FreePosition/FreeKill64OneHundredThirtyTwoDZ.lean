import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThirtyTwoDZFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThirtyTwoDZFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThirtyTwoDZFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThirtyTwoDZFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThirtyTwoDZFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThirtyTwoDZFastPow a n * oneHundredThirtyTwoDZFastPow a n * a else oneHundredThirtyTwoDZFastPow a n * oneHundredThirtyTwoDZFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThirtyTwoDZ_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1873 : Nat.Prime 1873 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2531 : Nat.Prime 2531 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3181 : Nat.Prime 3181 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3391 : Nat.Prime 3391 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3407 : Nat.Prime 3407 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3457 : Nat.Prime 3457 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3643 : Nat.Prime 3643 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3851 : Nat.Prime 3851 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3863 : Nat.Prime 3863 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3911 : Nat.Prime 3911 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4003 : Nat.Prime 4003 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4243 : Nat.Prime 4243 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4259 : Nat.Prime 4259 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4603 : Nat.Prime 4603 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4937 : Nat.Prime 4937 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4987 : Nat.Prime 4987 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4993 : Nat.Prime 4993 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_5171 : Nat.Prime 5171 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_5471 : Nat.Prime 5471 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_5521 : Nat.Prime 5521 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_6323 : Nat.Prime 6323 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7019 : Nat.Prime 7019 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7027 : Nat.Prime 7027 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7243 : Nat.Prime 7243 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7393 : Nat.Prime 7393 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7591 : Nat.Prime 7591 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7669 : Nat.Prime 7669 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7759 : Nat.Prime 7759 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7993 : Nat.Prime 7993 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_8237 : Nat.Prime 8237 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_8263 : Nat.Prime 8263 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_8317 : Nat.Prime 8317 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_8363 : Nat.Prime 8363 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_8741 : Nat.Prime 8741 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_9109 : Nat.Prime 9109 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_9187 : Nat.Prime 9187 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_9323 : Nat.Prime 9323 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_9829 : Nat.Prime 9829 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_9851 : Nat.Prime 9851 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_9931 : Nat.Prime 9931 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_10559 : Nat.Prime 10559 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_10709 : Nat.Prime 10709 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_11789 : Nat.Prime 11789 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_11801 : Nat.Prime 11801 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_12007 : Nat.Prime 12007 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_12227 : Nat.Prime 12227 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_12893 : Nat.Prime 12893 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_13313 : Nat.Prime 13313 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_13873 : Nat.Prime 13873 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_14411 : Nat.Prime 14411 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_14593 : Nat.Prime 14593 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_14629 : Nat.Prime 14629 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_14831 : Nat.Prime 14831 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_15461 : Nat.Prime 15461 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_16267 : Nat.Prime 16267 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_17231 : Nat.Prime 17231 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_18541 : Nat.Prime 18541 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_19163 : Nat.Prime 19163 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_19391 : Nat.Prime 19391 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_20357 : Nat.Prime 20357 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_21617 : Nat.Prime 21617 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_23189 : Nat.Prime 23189 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_23447 : Nat.Prime 23447 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_24821 : Nat.Prime 24821 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_26681 : Nat.Prime 26681 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_27397 : Nat.Prime 27397 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_31277 : Nat.Prime 31277 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_31699 : Nat.Prime 31699 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_33533 : Nat.Prime 33533 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_33617 : Nat.Prime 33617 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_35603 : Nat.Prime 35603 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_35863 : Nat.Prime 35863 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_36697 : Nat.Prime 36697 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_36709 : Nat.Prime 36709 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_37019 : Nat.Prime 37019 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_40759 : Nat.Prime 40759 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_42403 : Nat.Prime 42403 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_42557 : Nat.Prime 42557 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_43759 : Nat.Prime 43759 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_47981 : Nat.Prime 47981 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_48677 : Nat.Prime 48677 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_49297 : Nat.Prime 49297 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_49639 : Nat.Prime 49639 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_50377 : Nat.Prime 50377 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_52361 : Nat.Prime 52361 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_52639 : Nat.Prime 52639 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_52817 : Nat.Prime 52817 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_53279 : Nat.Prime 53279 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_53551 : Nat.Prime 53551 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_57839 : Nat.Prime 57839 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_60029 : Nat.Prime 60029 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_60779 : Nat.Prime 60779 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_61471 : Nat.Prime 61471 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_67181 : Nat.Prime 67181 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_68239 : Nat.Prime 68239 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_68351 : Nat.Prime 68351 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_70289 : Nat.Prime 70289 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_72977 : Nat.Prime 72977 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_74843 : Nat.Prime 74843 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_75239 : Nat.Prime 75239 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_80449 : Nat.Prime 80449 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_82193 : Nat.Prime 82193 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_83639 : Nat.Prime 83639 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_86381 : Nat.Prime 86381 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_88873 : Nat.Prime 88873 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_90359 : Nat.Prime 90359 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_91397 : Nat.Prime 91397 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_103349 : Nat.Prime 103349 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_104033 : Nat.Prime 104033 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_107201 : Nat.Prime 107201 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_113021 : Nat.Prime 113021 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_113093 : Nat.Prime 113093 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_115399 : Nat.Prime 115399 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_116089 : Nat.Prime 116089 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_121181 : Nat.Prime 121181 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_121661 : Nat.Prime 121661 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_123031 : Nat.Prime 123031 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_124343 : Nat.Prime 124343 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_124769 : Nat.Prime 124769 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_125287 : Nat.Prime 125287 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_128837 : Nat.Prime 128837 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_140689 : Nat.Prime 140689 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_141793 : Nat.Prime 141793 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_147793 : Nat.Prime 147793 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_148403 : Nat.Prime 148403 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_149173 : Nat.Prime 149173 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_153457 : Nat.Prime 153457 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_172097 : Nat.Prime 172097 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_172597 : Nat.Prime 172597 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_180233 : Nat.Prime 180233 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_183571 : Nat.Prime 183571 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_190181 : Nat.Prime 190181 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_201101 : Nat.Prime 201101 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_220021 : Nat.Prime 220021 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_222557 : Nat.Prime 222557 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_229841 : Nat.Prime 229841 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_235043 : Nat.Prime 235043 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_293269 : Nat.Prime 293269 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_298451 : Nat.Prime 298451 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_305633 : Nat.Prime 305633 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_310591 : Nat.Prime 310591 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_324301 : Nat.Prime 324301 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_327421 : Nat.Prime 327421 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_330791 : Nat.Prime 330791 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_331511 : Nat.Prime 331511 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_368873 : Nat.Prime 368873 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_376477 : Nat.Prime 376477 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_381443 : Nat.Prime 381443 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_382883 : Nat.Prime 382883 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_388459 : Nat.Prime 388459 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_389531 : Nat.Prime 389531 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_399181 : Nat.Prime 399181 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_454231 : Nat.Prime 454231 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_460711 : Nat.Prime 460711 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_467119 : Nat.Prime 467119 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_475523 : Nat.Prime 475523 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_479377 : Nat.Prime 479377 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_479909 : Nat.Prime 479909 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_480941 : Nat.Prime 480941 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_519119 : Nat.Prime 519119 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_556651 : Nat.Prime 556651 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_583459 : Nat.Prime 583459 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_590489 : Nat.Prime 590489 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_604243 : Nat.Prime 604243 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_606037 : Nat.Prime 606037 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_627271 : Nat.Prime 627271 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_638117 : Nat.Prime 638117 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_651733 : Nat.Prime 651733 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_663991 : Nat.Prime 663991 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_667631 : Nat.Prime 667631 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_721891 : Nat.Prime 721891 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_730853 : Nat.Prime 730853 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_754639 : Nat.Prime 754639 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_758111 : Nat.Prime 758111 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_758279 : Nat.Prime 758279 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_830329 : Nat.Prime 830329 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_845041 : Nat.Prime 845041 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_956269 : Nat.Prime 956269 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_972221 : Nat.Prime 972221 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1015981 : Nat.Prime 1015981 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1229519 : Nat.Prime 1229519 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1276397 : Nat.Prime 1276397 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1322917 : Nat.Prime 1322917 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1413233 : Nat.Prime 1413233 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1481899 : Nat.Prime 1481899 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1717169 : Nat.Prime 1717169 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_1901651 : Nat.Prime 1901651 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2016293 : Nat.Prime 2016293 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2040559 : Nat.Prime 2040559 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2159147 : Nat.Prime 2159147 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2186603 : Nat.Prime 2186603 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_2240471 : Nat.Prime 2240471 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3025219 : Nat.Prime 3025219 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3165203 : Nat.Prime 3165203 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3283807 : Nat.Prime 3283807 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3346157 : Nat.Prime 3346157 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3439229 : Nat.Prime 3439229 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3465031 : Nat.Prime 3465031 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3637297 : Nat.Prime 3637297 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3690257 : Nat.Prime 3690257 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3700691 : Nat.Prime 3700691 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3742237 : Nat.Prime 3742237 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_3755669 : Nat.Prime 3755669 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4049063 : Nat.Prime 4049063 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4174343 : Nat.Prime 4174343 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4186181 : Nat.Prime 4186181 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4362719 : Nat.Prime 4362719 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_4928953 : Nat.Prime 4928953 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_5009761 : Nat.Prime 5009761 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_5704513 : Nat.Prime 5704513 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_5815057 : Nat.Prime 5815057 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_5930381 : Nat.Prime 5930381 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_6007159 : Nat.Prime 6007159 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_6199273 : Nat.Prime 6199273 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_6336347 : Nat.Prime 6336347 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_6444443 : Nat.Prime 6444443 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7278961 : Nat.Prime 7278961 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7634603 : Nat.Prime 7634603 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_7772333 : Nat.Prime 7772333 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_8146423 : Nat.Prime 8146423 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_8348687 : Nat.Prime 8348687 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_9666227 : Nat.Prime 9666227 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_10263479 : Nat.Prime 10263479 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_10928963 : Nat.Prime 10928963 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_12069451 : Nat.Prime 12069451 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_14130299 : Nat.Prime 14130299 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_14201963 : Nat.Prime 14201963 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_14383849 : Nat.Prime 14383849 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_15899909 : Nat.Prime 15899909 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_16120057 : Nat.Prime 16120057 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_17570599 : Nat.Prime 17570599 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_19024693 : Nat.Prime 19024693 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_19630027 : Nat.Prime 19630027 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_19976597 : Nat.Prime 19976597 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_21063817 : Nat.Prime 21063817 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_22021211 : Nat.Prime 22021211 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_22307737 : Nat.Prime 22307737 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_24910663 : Nat.Prime 24910663 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_25657969 : Nat.Prime 25657969 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_26344529 : Nat.Prime 26344529 := by norm_num

private theorem prime_oneHundredThirtyTwoDZ_30612443 : Nat.Prime 30612443 := by
  apply lucas_primality 30612443 (2 : ZMod 30612443)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) = 30612443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_2186603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30612443) ^ 15306221 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 4373206 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 14 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_30954047 : Nat.Prime 30954047 := by
  apply lucas_primality 30954047 (5 : ZMod 30954047)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1289, 1), (12007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1289, 1), (12007, 1)] : List FactorBlock).map factorBlockValue).prod) = 30954047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_1289
      · exact prime_oneHundredThirtyTwoDZ_12007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 30954047) ^ 15477023 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 30954047) ^ 24014 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 30954047) ^ 2578 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_35322163 : Nat.Prime 35322163 := by
  apply lucas_primality 35322163 (2 : ZMod 35322163)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (137, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (137, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 35322163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_97
      · exact prime_oneHundredThirtyTwoDZ_137
      · exact prime_oneHundredThirtyTwoDZ_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35322163) ^ 17661081 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 35322163) ^ 11774054 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 35322163) ^ 364146 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 35322163) ^ 257826 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 35322163) ^ 79734 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_37763581 : Nat.Prime 37763581 := by
  apply lucas_primality 37763581 (10 : ZMod 37763581)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (79, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (79, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 37763581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_79
      · exact prime_oneHundredThirtyTwoDZ_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 37763581) ^ 18881790 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 37763581) ^ 12587860 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 37763581) ^ 7552716 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 37763581) ^ 1218180 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 37763581) ^ 478020 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 37763581) ^ 146940 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_40419853 : Nat.Prime 40419853 := by
  apply lucas_primality 40419853 (6 : ZMod 40419853)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (29, 1), (10559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (29, 1), (10559, 1)] : List FactorBlock).map factorBlockValue).prod) = 40419853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_29
      · exact prime_oneHundredThirtyTwoDZ_10559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 40419853) ^ 20209926 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 40419853) ^ 13473284 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 40419853) ^ 3674532 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 40419853) ^ 1393788 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 40419853) ^ 3828 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_41580373 : Nat.Prime 41580373 := by
  apply lucas_primality 41580373 (11 : ZMod 41580373)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3465031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3465031, 1)] : List FactorBlock).map factorBlockValue).prod) = 41580373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_3465031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 41580373) ^ 20790186 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 41580373) ^ 13860124 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 41580373) ^ 12 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_43001837 : Nat.Prime 43001837 := by
  apply lucas_primality 43001837 (2 : ZMod 43001837)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) = 43001837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_239
      · exact prime_oneHundredThirtyTwoDZ_1451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43001837) ^ 21500918 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 1387156 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 179924 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 29636 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_45068029 : Nat.Prime 45068029 := by
  apply lucas_primality 45068029 (7 : ZMod 45068029)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3755669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3755669, 1)] : List FactorBlock).map factorBlockValue).prod) = 45068029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_3755669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 45068029) ^ 22534014 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 45068029) ^ 15022676 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 45068029) ^ 12 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_47024249 : Nat.Prime 47024249 := by
  apply lucas_primality 47024249 (3 : ZMod 47024249)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1277, 1), (4603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1277, 1), (4603, 1)] : List FactorBlock).map factorBlockValue).prod) = 47024249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_1277
      · exact prime_oneHundredThirtyTwoDZ_4603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47024249) ^ 23512124 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 47024249) ^ 36824 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 47024249) ^ 10216 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_49471423 : Nat.Prime 49471423 := by
  apply lucas_primality 49471423 (3 : ZMod 49471423)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) = 49471423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_8237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49471423) ^ 24735711 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 16490474 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 7067346 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 4497402 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 3805494 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 6006 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_51280043 : Nat.Prime 51280043 := by
  apply lucas_primality 51280043 (2 : ZMod 51280043)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (313, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (313, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 51280043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_313
      · exact prime_oneHundredThirtyTwoDZ_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51280043) ^ 25640021 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51280043) ^ 4661822 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51280043) ^ 163834 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51280043) ^ 75746 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_51515071 : Nat.Prime 51515071 := by
  apply lucas_primality 51515071 (3 : ZMod 51515071)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1717169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1717169, 1)] : List FactorBlock).map factorBlockValue).prod) = 51515071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_1717169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 51515071) ^ 25757535 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 51515071) ^ 17171690 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 51515071) ^ 10303014 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 51515071) ^ 30 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_55570169 : Nat.Prime 55570169 := by
  apply lucas_primality 55570169 (3 : ZMod 55570169)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (147793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (147793, 1)] : List FactorBlock).map factorBlockValue).prod) = 55570169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_47
      · exact prime_oneHundredThirtyTwoDZ_147793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55570169) ^ 27785084 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 55570169) ^ 1182344 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 55570169) ^ 376 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_1811
      · exact prime_oneHundredThirtyTwoDZ_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_66858343 : Nat.Prime 66858343 := by
  apply lucas_primality 66858343 (5 : ZMod 66858343)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1453, 1), (7669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1453, 1), (7669, 1)] : List FactorBlock).map factorBlockValue).prod) = 66858343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_1453
      · exact prime_oneHundredThirtyTwoDZ_7669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66858343) ^ 33429171 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 66858343) ^ 22286114 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 66858343) ^ 46014 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 66858343) ^ 8718 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_70496453 : Nat.Prime 70496453 := by
  apply lucas_primality 70496453 (2 : ZMod 70496453)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (467, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (467, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) = 70496453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_467
      · exact prime_oneHundredThirtyTwoDZ_2903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70496453) ^ 35248226 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 70496453) ^ 5422804 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 70496453) ^ 150956 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 70496453) ^ 24284 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_80035261 : Nat.Prime 80035261 := by
  apply lucas_primality 80035261 (2 : ZMod 80035261)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (641, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (641, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) = 80035261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_641
      · exact prime_oneHundredThirtyTwoDZ_2081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 80035261) ^ 40017630 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 80035261) ^ 26678420 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 80035261) ^ 16007052 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 80035261) ^ 124860 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 80035261) ^ 38460 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_80838911 : Nat.Prime 80838911 := by
  apply lucas_primality 80838911 (29 : ZMod 80838911)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (475523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (475523, 1)] : List FactorBlock).map factorBlockValue).prod) = 80838911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_475523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 80838911) ^ 40419455 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (29 : ZMod 80838911) ^ 16167782 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (29 : ZMod 80838911) ^ 4755230 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (29 : ZMod 80838911) ^ 170 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_84199277 : Nat.Prime 84199277 := by
  apply lucas_primality 84199277 (2 : ZMod 84199277)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (61, 1), (49297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (61, 1), (49297, 1)] : List FactorBlock).map factorBlockValue).prod) = 84199277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_61
      · exact prime_oneHundredThirtyTwoDZ_49297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84199277) ^ 42099638 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 84199277) ^ 12028468 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 84199277) ^ 1380316 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 84199277) ^ 1708 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_84917759 : Nat.Prime 84917759 := by
  apply lucas_primality 84917759 (11 : ZMod 84917759)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (389531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (389531, 1)] : List FactorBlock).map factorBlockValue).prod) = 84917759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_109
      · exact prime_oneHundredThirtyTwoDZ_389531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 84917759) ^ 42458879 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 84917759) ^ 779062 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 84917759) ^ 218 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_89230949 : Nat.Prime 89230949 := by
  apply lucas_primality 89230949 (2 : ZMod 89230949)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (22307737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (22307737, 1)] : List FactorBlock).map factorBlockValue).prod) = 89230949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_22307737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 89230949) ^ 44615474 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 89230949) ^ 4 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_93410561 : Nat.Prime 93410561 := by
  apply lucas_primality 93410561 (3 : ZMod 93410561)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (72977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (72977, 1)] : List FactorBlock).map factorBlockValue).prod) = 93410561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_72977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 93410561) ^ 46705280 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 93410561) ^ 18682112 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 93410561) ^ 1280 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_94480049 : Nat.Prime 94480049 := by
  apply lucas_primality 94480049 (3 : ZMod 94480049)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (454231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (454231, 1)] : List FactorBlock).map factorBlockValue).prod) = 94480049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_454231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 94480049) ^ 47240024 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 94480049) ^ 7267696 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 94480049) ^ 208 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_96720343 : Nat.Prime 96720343 := by
  apply lucas_primality 96720343 (6 : ZMod 96720343)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (16120057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (16120057, 1)] : List FactorBlock).map factorBlockValue).prod) = 96720343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_16120057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 96720343) ^ 48360171 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 96720343) ^ 32240114 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 96720343) ^ 6 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_19
      · exact prime_oneHundredThirtyTwoDZ_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_103978129 : Nat.Prime 103978129 := by
  apply lucas_primality 103978129 (7 : ZMod 103978129)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (50377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (50377, 1)] : List FactorBlock).map factorBlockValue).prod) = 103978129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_43
      · exact prime_oneHundredThirtyTwoDZ_50377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 103978129) ^ 51989064 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 103978129) ^ 34659376 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 103978129) ^ 2418096 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 103978129) ^ 2064 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_117238469 : Nat.Prime 117238469 := by
  apply lucas_primality 117238469 (2 : ZMod 117238469)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (97, 1), (7027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (97, 1), (7027, 1)] : List FactorBlock).map factorBlockValue).prod) = 117238469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_43
      · exact prime_oneHundredThirtyTwoDZ_97
      · exact prime_oneHundredThirtyTwoDZ_7027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 117238469) ^ 58619234 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 117238469) ^ 2726476 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 117238469) ^ 1208644 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 117238469) ^ 16684 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_119623961 : Nat.Prime 119623961 := by
  apply lucas_primality 119623961 (3 : ZMod 119623961)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (37, 1), (131, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (37, 1), (131, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 119623961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_37
      · exact prime_oneHundredThirtyTwoDZ_131
      · exact prime_oneHundredThirtyTwoDZ_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 119623961) ^ 59811980 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 119623961) ^ 23924792 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 119623961) ^ 3233080 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 119623961) ^ 913160 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 119623961) ^ 193880 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_133272001 : Nat.Prime 133272001 := by
  apply lucas_primality 133272001 (23 : ZMod 133272001)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 3), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 3), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 133272001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 133272001) ^ 66636000 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 133272001) ^ 44424000 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 133272001) ^ 26654400 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 133272001) ^ 216000 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_135346963 : Nat.Prime 135346963 := by
  apply lucas_primality 135346963 (2 : ZMod 135346963)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (37, 1), (35863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (37, 1), (35863, 1)] : List FactorBlock).map factorBlockValue).prod) = 135346963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_37
      · exact prime_oneHundredThirtyTwoDZ_35863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135346963) ^ 67673481 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 135346963) ^ 45115654 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 135346963) ^ 7961586 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 135346963) ^ 3658026 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 135346963) ^ 3774 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_137658557 : Nat.Prime 137658557 := by
  apply lucas_primality 137658557 (2 : ZMod 137658557)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (101, 1), (48677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (101, 1), (48677, 1)] : List FactorBlock).map factorBlockValue).prod) = 137658557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_101
      · exact prime_oneHundredThirtyTwoDZ_48677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 137658557) ^ 68829278 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 137658557) ^ 19665508 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 137658557) ^ 1362956 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 137658557) ^ 2828 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_150555719 : Nat.Prime 150555719 := by
  apply lucas_primality 150555719 (13 : ZMod 150555719)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (730853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (730853, 1)] : List FactorBlock).map factorBlockValue).prod) = 150555719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_103
      · exact prime_oneHundredThirtyTwoDZ_730853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 150555719) ^ 75277859 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 150555719) ^ 1461706 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 150555719) ^ 206 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_163361827 : Nat.Prime 163361827 := by
  apply lucas_primality 163361827 (2 : ZMod 163361827)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (3025219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (3025219, 1)] : List FactorBlock).map factorBlockValue).prod) = 163361827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_3025219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 163361827) ^ 81680913 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 163361827) ^ 54453942 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 163361827) ^ 54 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_164535439 : Nat.Prime 164535439 := by
  apply lucas_primality 164535439 (3 : ZMod 164535439)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (583459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (583459, 1)] : List FactorBlock).map factorBlockValue).prod) = 164535439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_47
      · exact prime_oneHundredThirtyTwoDZ_583459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 164535439) ^ 82267719 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 164535439) ^ 54845146 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 164535439) ^ 3500754 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 164535439) ^ 282 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_180272117 : Nat.Prime 180272117 := by
  apply lucas_primality 180272117 (2 : ZMod 180272117)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (45068029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (45068029, 1)] : List FactorBlock).map factorBlockValue).prod) = 180272117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_45068029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 180272117) ^ 90136058 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 180272117) ^ 4 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_187894423 : Nat.Prime 187894423 := by
  apply lucas_primality 187894423 (3 : ZMod 187894423)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (593, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (593, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) = 187894423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_29
      · exact prime_oneHundredThirtyTwoDZ_593
      · exact prime_oneHundredThirtyTwoDZ_607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 187894423) ^ 93947211 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 187894423) ^ 62631474 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 187894423) ^ 6479118 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 187894423) ^ 316854 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 187894423) ^ 309546 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_188960099 : Nat.Prime 188960099 := by
  apply lucas_primality 188960099 (2 : ZMod 188960099)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (94480049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (94480049, 1)] : List FactorBlock).map factorBlockValue).prod) = 188960099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_94480049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 188960099) ^ 94480049 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 188960099) ^ 2 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_200272519 : Nat.Prime 200272519 := by
  apply lucas_primality 200272519 (15 : ZMod 200272519)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) = 200272519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_181
      · exact prime_oneHundredThirtyTwoDZ_61471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 200272519) ^ 100136259 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 66757506 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 1106478 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 3258 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_203584081 : Nat.Prime 203584081 := by
  apply lucas_primality 203584081 (11 : ZMod 203584081)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (121181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (121181, 1)] : List FactorBlock).map factorBlockValue).prod) = 203584081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_121181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 203584081) ^ 101792040 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 203584081) ^ 67861360 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 203584081) ^ 40716816 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 203584081) ^ 29083440 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 203584081) ^ 1680 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_205584779 : Nat.Prime 205584779 := by
  apply lucas_primality 205584779 (2 : ZMod 205584779)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1201, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1201, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) = 205584779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_1201
      · exact prime_oneHundredThirtyTwoDZ_12227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 205584779) ^ 102792389 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 205584779) ^ 29369254 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 205584779) ^ 171178 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 205584779) ^ 16814 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_213150073 : Nat.Prime 213150073 := by
  apply lucas_primality 213150073 (5 : ZMod 213150073)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) = 213150073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_73
      · exact prime_oneHundredThirtyTwoDZ_121661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 213150073) ^ 106575036 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 71050024 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 2919864 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 1752 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_266346061 : Nat.Prime 266346061 := by
  apply lucas_primality 266346061 (2 : ZMod 266346061)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (59, 1), (75239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (59, 1), (75239, 1)] : List FactorBlock).map factorBlockValue).prod) = 266346061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_59
      · exact prime_oneHundredThirtyTwoDZ_75239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 266346061) ^ 133173030 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 266346061) ^ 88782020 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 266346061) ^ 53269212 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 266346061) ^ 4514340 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 266346061) ^ 3540 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_274572647 : Nat.Prime 274572647 := by
  apply lucas_primality 274572647 (5 : ZMod 274572647)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2287, 1), (60029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2287, 1), (60029, 1)] : List FactorBlock).map factorBlockValue).prod) = 274572647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_2287
      · exact prime_oneHundredThirtyTwoDZ_60029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 274572647) ^ 137286323 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 274572647) ^ 120058 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 274572647) ^ 4574 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_340058183 : Nat.Prime 340058183 := by
  apply lucas_primality 340058183 (5 : ZMod 340058183)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (59, 1), (70289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (59, 1), (70289, 1)] : List FactorBlock).map factorBlockValue).prod) = 340058183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_41
      · exact prime_oneHundredThirtyTwoDZ_59
      · exact prime_oneHundredThirtyTwoDZ_70289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 340058183) ^ 170029091 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 340058183) ^ 8294102 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 340058183) ^ 5763698 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 340058183) ^ 4838 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_342432449 : Nat.Prime 342432449 := by
  apply lucas_primality 342432449 (3 : ZMod 342432449)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (31, 1), (172597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (31, 1), (172597, 1)] : List FactorBlock).map factorBlockValue).prod) = 342432449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_172597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 342432449) ^ 171216224 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 342432449) ^ 11046208 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 342432449) ^ 1984 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_357197261 : Nat.Prime 357197261 := by
  apply lucas_primality 357197261 (2 : ZMod 357197261)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (37, 1), (9851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (37, 1), (9851, 1)] : List FactorBlock).map factorBlockValue).prod) = 357197261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_37
      · exact prime_oneHundredThirtyTwoDZ_9851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 357197261) ^ 178598630 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 357197261) ^ 71439452 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 357197261) ^ 51028180 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 357197261) ^ 9653980 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 357197261) ^ 36260 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_382693673 : Nat.Prime 382693673 := by
  apply lucas_primality 382693673 (3 : ZMod 382693673)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (127, 1), (9187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (127, 1), (9187, 1)] : List FactorBlock).map factorBlockValue).prod) = 382693673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_41
      · exact prime_oneHundredThirtyTwoDZ_127
      · exact prime_oneHundredThirtyTwoDZ_9187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 382693673) ^ 191346836 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 382693673) ^ 9333992 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 382693673) ^ 3013336 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 382693673) ^ 41656 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_393763493 : Nat.Prime 393763493 := by
  apply lucas_primality 393763493 (2 : ZMod 393763493)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (149, 1), (8363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (149, 1), (8363, 1)] : List FactorBlock).map factorBlockValue).prod) = 393763493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_79
      · exact prime_oneHundredThirtyTwoDZ_149
      · exact prime_oneHundredThirtyTwoDZ_8363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 393763493) ^ 196881746 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 393763493) ^ 4984348 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 393763493) ^ 2642708 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 393763493) ^ 47084 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_396380419 : Nat.Prime 396380419 := by
  apply lucas_primality 396380419 (2 : ZMod 396380419)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1303, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1303, 1), (7243, 1)] : List FactorBlock).map factorBlockValue).prod) = 396380419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_1303
      · exact prime_oneHundredThirtyTwoDZ_7243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 396380419) ^ 198190209 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 396380419) ^ 132126806 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 396380419) ^ 56625774 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 396380419) ^ 304206 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 396380419) ^ 54726 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_399315911 : Nat.Prime 399315911 := by
  apply lucas_primality 399315911 (7 : ZMod 399315911)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (5704513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (5704513, 1)] : List FactorBlock).map factorBlockValue).prod) = 399315911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_5704513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 399315911) ^ 199657955 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 399315911) ^ 79863182 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 399315911) ^ 57045130 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 399315911) ^ 70 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_468866873 : Nat.Prime 468866873 := by
  apply lucas_primality 468866873 (3 : ZMod 468866873)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (179, 1), (327421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (179, 1), (327421, 1)] : List FactorBlock).map factorBlockValue).prod) = 468866873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_179
      · exact prime_oneHundredThirtyTwoDZ_327421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 468866873) ^ 234433436 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 468866873) ^ 2619368 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 468866873) ^ 1432 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_503630299 : Nat.Prime 503630299 := by
  apply lucas_primality 503630299 (2 : ZMod 503630299)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (29, 1), (107201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (29, 1), (107201, 1)] : List FactorBlock).map factorBlockValue).prod) = 503630299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_29
      · exact prime_oneHundredThirtyTwoDZ_107201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 503630299) ^ 251815149 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 503630299) ^ 167876766 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 503630299) ^ 17366562 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 503630299) ^ 4698 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_523642733 : Nat.Prime 523642733 := by
  apply lucas_primality 523642733 (2 : ZMod 523642733)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (337, 1), (388459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (337, 1), (388459, 1)] : List FactorBlock).map factorBlockValue).prod) = 523642733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_337
      · exact prime_oneHundredThirtyTwoDZ_388459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 523642733) ^ 261821366 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 523642733) ^ 1553836 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 523642733) ^ 1348 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_541387853 : Nat.Prime 541387853 := by
  apply lucas_primality 541387853 (2 : ZMod 541387853)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (135346963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (135346963, 1)] : List FactorBlock).map factorBlockValue).prod) = 541387853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_135346963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 541387853) ^ 270693926 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 541387853) ^ 4 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_559319647 : Nat.Prime 559319647 := by
  apply lucas_primality 559319647 (3 : ZMod 559319647)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) = 559319647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_47
      · exact prime_oneHundredThirtyTwoDZ_59
      · exact prime_oneHundredThirtyTwoDZ_33617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 559319647) ^ 279659823 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 186439882 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 11900418 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 9479994 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 16638 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_561631199 : Nat.Prime 561631199 := by
  apply lucas_primality 561631199 (17 : ZMod 561631199)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (389, 1), (721891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (389, 1), (721891, 1)] : List FactorBlock).map factorBlockValue).prod) = 561631199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_389
      · exact prime_oneHundredThirtyTwoDZ_721891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 561631199) ^ 280815599 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (17 : ZMod 561631199) ^ 1443782 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (17 : ZMod 561631199) ^ 778 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_572551487 : Nat.Prime 572551487 := by
  apply lucas_primality 572551487 (5 : ZMod 572551487)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (22021211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (22021211, 1)] : List FactorBlock).map factorBlockValue).prod) = 572551487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_22021211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 572551487) ^ 286275743 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 572551487) ^ 44042422 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 572551487) ^ 26 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_19
      · exact prime_oneHundredThirtyTwoDZ_61
      · exact prime_oneHundredThirtyTwoDZ_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_17203
      · exact prime_oneHundredThirtyTwoDZ_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_729919451 : Nat.Prime 729919451 := by
  apply lucas_primality 729919451 (2 : ZMod 729919451)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 2), (86381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 2), (86381, 1)] : List FactorBlock).map factorBlockValue).prod) = 729919451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_86381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 729919451) ^ 364959725 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 729919451) ^ 145983890 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 729919451) ^ 56147650 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 729919451) ^ 8450 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1024189693 : Nat.Prime 1024189693 := by
  apply lucas_primality 1024189693 (5 : ZMod 1024189693)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (101, 1), (845041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (101, 1), (845041, 1)] : List FactorBlock).map factorBlockValue).prod) = 1024189693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_101
      · exact prime_oneHundredThirtyTwoDZ_845041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1024189693) ^ 512094846 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1024189693) ^ 341396564 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1024189693) ^ 10140492 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1024189693) ^ 1212 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1027139401 : Nat.Prime 1027139401 := by
  apply lucas_primality 1027139401 (23 : ZMod 1027139401)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 2), (7, 1), (29, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 2), (7, 1), (29, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) = 1027139401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_29
      · exact prime_oneHundredThirtyTwoDZ_937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1027139401) ^ 513569700 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1027139401) ^ 342379800 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1027139401) ^ 205427880 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1027139401) ^ 146734200 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1027139401) ^ 35418600 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 1027139401) ^ 1096200 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1101268457 : Nat.Prime 1101268457 := by
  apply lucas_primality 1101268457 (3 : ZMod 1101268457)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137658557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137658557, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101268457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_137658557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1101268457) ^ 550634228 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1101268457) ^ 8 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1124518337 : Nat.Prime 1124518337 := by
  apply lucas_primality 1124518337 (3 : ZMod 1124518337)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (17570599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (17570599, 1)] : List FactorBlock).map factorBlockValue).prod) = 1124518337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_17570599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1124518337) ^ 562259168 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1124518337) ^ 64 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1160644117 : Nat.Prime 1160644117 := by
  apply lucas_primality 1160644117 (6 : ZMod 1160644117)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (96720343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (96720343, 1)] : List FactorBlock).map factorBlockValue).prod) = 1160644117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_96720343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1160644117) ^ 580322058 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160644117) ^ 386881372 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160644117) ^ 12 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1167580853 : Nat.Prime 1167580853 := by
  apply lucas_primality 1167580853 (2 : ZMod 1167580853)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (281, 1), (10709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (281, 1), (10709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1167580853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_97
      · exact prime_oneHundredThirtyTwoDZ_281
      · exact prime_oneHundredThirtyTwoDZ_10709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1167580853) ^ 583790426 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167580853) ^ 12036916 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167580853) ^ 4155092 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167580853) ^ 109028 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1294332317 : Nat.Prime 1294332317 := by
  apply lucas_primality 1294332317 (2 : ZMod 1294332317)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8741, 1), (37019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8741, 1), (37019, 1)] : List FactorBlock).map factorBlockValue).prod) = 1294332317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_8741
      · exact prime_oneHundredThirtyTwoDZ_37019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1294332317) ^ 647166158 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1294332317) ^ 148076 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1294332317) ^ 34964 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1631470259 : Nat.Prime 1631470259 := by
  apply lucas_primality 1631470259 (2 : ZMod 1631470259)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (523, 1), (141793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (523, 1), (141793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1631470259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_523
      · exact prime_oneHundredThirtyTwoDZ_141793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1631470259) ^ 815735129 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1631470259) ^ 148315478 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1631470259) ^ 3119446 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1631470259) ^ 11506 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2179807673 : Nat.Prime 2179807673 := by
  apply lucas_primality 2179807673 (3 : ZMod 2179807673)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (61, 1), (638117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (61, 1), (638117, 1)] : List FactorBlock).map factorBlockValue).prod) = 2179807673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_61
      · exact prime_oneHundredThirtyTwoDZ_638117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2179807673) ^ 1089903836 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2179807673) ^ 311401096 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2179807673) ^ 35734552 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2179807673) ^ 3416 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2267521189 : Nat.Prime 2267521189 := by
  apply lucas_primality 2267521189 (2 : ZMod 2267521189)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (188960099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (188960099, 1)] : List FactorBlock).map factorBlockValue).prod) = 2267521189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_188960099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2267521189) ^ 1133760594 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267521189) ^ 755840396 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267521189) ^ 12 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2354537833 : Nat.Prime 2354537833 := by
  apply lucas_primality 2354537833 (5 : ZMod 2354537833)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (1489, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (1489, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) = 2354537833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_41
      · exact prime_oneHundredThirtyTwoDZ_1489
      · exact prime_oneHundredThirtyTwoDZ_1607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2354537833) ^ 1177268916 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2354537833) ^ 784845944 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2354537833) ^ 57427752 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2354537833) ^ 1581288 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2354537833) ^ 1465176 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_47
      · exact prime_oneHundredThirtyTwoDZ_71
      · exact prime_oneHundredThirtyTwoDZ_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2495475097 : Nat.Prime 2495475097 := by
  apply lucas_primality 2495475097 (10 : ZMod 2495475097)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (103978129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (103978129, 1)] : List FactorBlock).map factorBlockValue).prod) = 2495475097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_103978129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 2495475097) ^ 1247737548 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2495475097) ^ 831825032 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2495475097) ^ 24 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_3262940519 : Nat.Prime 3262940519 := by
  apply lucas_primality 3262940519 (11 : ZMod 3262940519)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1631470259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1631470259, 1)] : List FactorBlock).map factorBlockValue).prod) = 3262940519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_1631470259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 3262940519) ^ 1631470259 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 3262940519) ^ 2 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_4914242863 : Nat.Prime 4914242863 := by
  apply lucas_primality 4914242863 (3 : ZMod 4914242863)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (19976597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (19976597, 1)] : List FactorBlock).map factorBlockValue).prod) = 4914242863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_41
      · exact prime_oneHundredThirtyTwoDZ_19976597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4914242863) ^ 2457121431 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 1638080954 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 119859582 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 246 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_5429792839 : Nat.Prime 5429792839 := by
  apply lucas_primality 5429792839 (6 : ZMod 5429792839)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) = 5429792839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_709
      · exact prime_oneHundredThirtyTwoDZ_1276397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5429792839) ^ 2714896419 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 1809930946 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 7658382 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 4254 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_5839355609 : Nat.Prime 5839355609 := by
  apply lucas_primality 5839355609 (3 : ZMod 5839355609)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (729919451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (729919451, 1)] : List FactorBlock).map factorBlockValue).prod) = 5839355609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_729919451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5839355609) ^ 2919677804 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5839355609) ^ 8 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_6467112881 : Nat.Prime 6467112881 := by
  apply lucas_primality 6467112881 (3 : ZMod 6467112881)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (80838911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (80838911, 1)] : List FactorBlock).map factorBlockValue).prod) = 6467112881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_80838911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6467112881) ^ 3233556440 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6467112881) ^ 1293422576 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6467112881) ^ 80 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_7661518289 : Nat.Prime 7661518289 := by
  apply lucas_primality 7661518289 (3 : ZMod 7661518289)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3851, 1), (124343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3851, 1), (124343, 1)] : List FactorBlock).map factorBlockValue).prod) = 7661518289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3851
      · exact prime_oneHundredThirtyTwoDZ_124343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7661518289) ^ 3830759144 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 7661518289) ^ 1989488 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 7661518289) ^ 61616 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_7875269861 : Nat.Prime 7875269861 := by
  apply lucas_primality 7875269861 (2 : ZMod 7875269861)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (393763493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (393763493, 1)] : List FactorBlock).map factorBlockValue).prod) = 7875269861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_393763493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7875269861) ^ 3937634930 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7875269861) ^ 1575053972 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7875269861) ^ 20 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_8015720819 : Nat.Prime 8015720819 := by
  apply lucas_primality 8015720819 (2 : ZMod 8015720819)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (572551487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (572551487, 1)] : List FactorBlock).map factorBlockValue).prod) = 8015720819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_572551487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8015720819) ^ 4007860409 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8015720819) ^ 1145102974 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8015720819) ^ 14 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_9196921663 : Nat.Prime 9196921663 := by
  apply lucas_primality 9196921663 (3 : ZMod 9196921663)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (12069451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (12069451, 1)] : List FactorBlock).map factorBlockValue).prod) = 9196921663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_127
      · exact prime_oneHundredThirtyTwoDZ_12069451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9196921663) ^ 4598460831 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9196921663) ^ 3065640554 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9196921663) ^ 72416706 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 9196921663) ^ 762 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_9651195503 : Nat.Prime 9651195503 := by
  apply lucas_primality 9651195503 (5 : ZMod 9651195503)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (109, 1), (151, 1), (1187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (109, 1), (151, 1), (1187, 1)] : List FactorBlock).map factorBlockValue).prod) = 9651195503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_19
      · exact prime_oneHundredThirtyTwoDZ_109
      · exact prime_oneHundredThirtyTwoDZ_151
      · exact prime_oneHundredThirtyTwoDZ_1187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9651195503) ^ 4825597751 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 9651195503) ^ 742399654 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 9651195503) ^ 507957658 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 9651195503) ^ 88543078 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 9651195503) ^ 63915202 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 9651195503) ^ 8130746 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_11819834233 : Nat.Prime 11819834233 := by
  apply lucas_primality 11819834233 (5 : ZMod 11819834233)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4003, 1), (123031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4003, 1), (123031, 1)] : List FactorBlock).map factorBlockValue).prod) = 11819834233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_4003
      · exact prime_oneHundredThirtyTwoDZ_123031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11819834233) ^ 5909917116 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11819834233) ^ 3939944744 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11819834233) ^ 2952744 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11819834233) ^ 96072 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_12474111901 : Nat.Prime 12474111901 := by
  apply lucas_primality 12474111901 (6 : ZMod 12474111901)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (41580373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (41580373, 1)] : List FactorBlock).map factorBlockValue).prod) = 12474111901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_41580373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 12474111901) ^ 6237055950 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 12474111901) ^ 4158037300 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 12474111901) ^ 2494822380 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 12474111901) ^ 300 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_12934225763 : Nat.Prime 12934225763 := by
  apply lucas_primality 12934225763 (2 : ZMod 12934225763)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6467112881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6467112881, 1)] : List FactorBlock).map factorBlockValue).prod) = 12934225763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_6467112881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 12934225763) ^ 6467112881 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12934225763) ^ 2 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_12995087869 : Nat.Prime 12995087869 := by
  apply lucas_primality 12995087869 (2 : ZMod 12995087869)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (641, 1), (80449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (641, 1), (80449, 1)] : List FactorBlock).map factorBlockValue).prod) = 12995087869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_641
      · exact prime_oneHundredThirtyTwoDZ_80449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12995087869) ^ 6497543934 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12995087869) ^ 4331695956 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12995087869) ^ 1856441124 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12995087869) ^ 20273148 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12995087869) ^ 161532 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_15696613913 : Nat.Prime 15696613913 := by
  apply lucas_primality 15696613913 (3 : ZMod 15696613913)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (16267, 1), (17231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (16267, 1), (17231, 1)] : List FactorBlock).map factorBlockValue).prod) = 15696613913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_16267
      · exact prime_oneHundredThirtyTwoDZ_17231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15696613913) ^ 7848306956 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15696613913) ^ 2242373416 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15696613913) ^ 964936 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15696613913) ^ 910952 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_20969238383 : Nat.Prime 20969238383 := by
  apply lucas_primality 20969238383 (5 : ZMod 20969238383)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (80035261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (80035261, 1)] : List FactorBlock).map factorBlockValue).prod) = 20969238383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_131
      · exact prime_oneHundredThirtyTwoDZ_80035261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 20969238383) ^ 10484619191 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20969238383) ^ 160070522 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20969238383) ^ 262 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_23668773979 : Nat.Prime 23668773979 := by
  apply lucas_primality 23668773979 (2 : ZMod 23668773979)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (37, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (37, 1), (3439229, 1)] : List FactorBlock).map factorBlockValue).prod) = 23668773979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_37
      · exact prime_oneHundredThirtyTwoDZ_3439229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23668773979) ^ 11834386989 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23668773979) ^ 7889591326 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23668773979) ^ 763508838 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23668773979) ^ 639696594 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 23668773979) ^ 6882 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_27918548017 : Nat.Prime 27918548017 := by
  apply lucas_primality 27918548017 (5 : ZMod 27918548017)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) = 27918548017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_19
      · exact prime_oneHundredThirtyTwoDZ_30612443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27918548017) ^ 13959274008 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 9306182672 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 1469397264 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 912 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_29485457179 : Nat.Prime 29485457179 := by
  apply lucas_primality 29485457179 (2 : ZMod 29485457179)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4914242863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4914242863, 1)] : List FactorBlock).map factorBlockValue).prod) = 29485457179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_4914242863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29485457179) ^ 14742728589 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 29485457179) ^ 9828485726 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 29485457179) ^ 6 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_33446361583 : Nat.Prime 33446361583 := by
  apply lucas_primality 33446361583 (3 : ZMod 33446361583)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (211, 1), (382883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (211, 1), (382883, 1)] : List FactorBlock).map factorBlockValue).prod) = 33446361583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_23
      · exact prime_oneHundredThirtyTwoDZ_211
      · exact prime_oneHundredThirtyTwoDZ_382883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33446361583) ^ 16723180791 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 11148787194 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 1454189634 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 158513562 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 87354 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_56645794981 : Nat.Prime 56645794981 := by
  apply lucas_primality 56645794981 (7 : ZMod 56645794981)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (59, 1), (1907, 1), (2797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (59, 1), (1907, 1), (2797, 1)] : List FactorBlock).map factorBlockValue).prod) = 56645794981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_59
      · exact prime_oneHundredThirtyTwoDZ_1907
      · exact prime_oneHundredThirtyTwoDZ_2797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 56645794981) ^ 28322897490 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 18881931660 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 11329158996 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 960098220 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 29704140 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 20252340 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_60277551527 : Nat.Prime 60277551527 := by
  apply lucas_primality 60277551527 (5 : ZMod 60277551527)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (3181, 1), (305633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (3181, 1), (305633, 1)] : List FactorBlock).map factorBlockValue).prod) = 60277551527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_3181
      · exact prime_oneHundredThirtyTwoDZ_305633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 60277551527) ^ 30138775763 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 60277551527) ^ 1944437146 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 60277551527) ^ 18949246 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 60277551527) ^ 197222 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_64002540631 : Nat.Prime 64002540631 := by
  apply lucas_primality 64002540631 (3 : ZMod 64002540631)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (89, 1), (180233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (89, 1), (180233, 1)] : List FactorBlock).map factorBlockValue).prod) = 64002540631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_19
      · exact prime_oneHundredThirtyTwoDZ_89
      · exact prime_oneHundredThirtyTwoDZ_180233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64002540631) ^ 32001270315 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 21334180210 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 12800508126 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 9143220090 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 3368554770 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 719129670 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 355110 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_66076107421 : Nat.Prime 66076107421 := by
  apply lucas_primality 66076107421 (2 : ZMod 66076107421)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1101268457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1101268457, 1)] : List FactorBlock).map factorBlockValue).prod) = 66076107421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_1101268457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66076107421) ^ 33038053710 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 66076107421) ^ 22025369140 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 66076107421) ^ 13215221484 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 66076107421) ^ 60 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_74166855821 : Nat.Prime 74166855821 := by
  apply lucas_primality 74166855821 (2 : ZMod 74166855821)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (119623961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (119623961, 1)] : List FactorBlock).map factorBlockValue).prod) = 74166855821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_119623961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74166855821) ^ 37083427910 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 74166855821) ^ 14833371164 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 74166855821) ^ 2392479220 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 74166855821) ^ 620 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_108564107459 : Nat.Prime 108564107459 := by
  apply lucas_primality 108564107459 (2 : ZMod 108564107459)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (1024189693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (1024189693, 1)] : List FactorBlock).map factorBlockValue).prod) = 108564107459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_53
      · exact prime_oneHundredThirtyTwoDZ_1024189693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 108564107459) ^ 54282053729 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 108564107459) ^ 2048379386 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 108564107459) ^ 106 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_137907604409 : Nat.Prime 137907604409 := by
  apply lucas_primality 137907604409 (3 : ZMod 137907604409)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (17, 1), (149, 1), (972221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (17, 1), (149, 1), (972221, 1)] : List FactorBlock).map factorBlockValue).prod) = 137907604409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_149
      · exact prime_oneHundredThirtyTwoDZ_972221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 137907604409) ^ 68953802204 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 137907604409) ^ 19701086344 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 137907604409) ^ 8112212024 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 137907604409) ^ 925554392 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 137907604409) ^ 141848 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_149153487139 : Nat.Prime 149153487139 := by
  apply lucas_primality 149153487139 (10 : ZMod 149153487139)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (151, 1), (2003, 1), (27397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (151, 1), (2003, 1), (27397, 1)] : List FactorBlock).map factorBlockValue).prod) = 149153487139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_151
      · exact prime_oneHundredThirtyTwoDZ_2003
      · exact prime_oneHundredThirtyTwoDZ_27397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 149153487139) ^ 74576743569 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 149153487139) ^ 49717829046 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 149153487139) ^ 987771438 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 149153487139) ^ 74465046 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 149153487139) ^ 5444154 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_186461254597 : Nat.Prime 186461254597 := by
  apply lucas_primality 186461254597 (6 : ZMod 186461254597)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (463, 1), (491, 1), (68351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (463, 1), (491, 1), (68351, 1)] : List FactorBlock).map factorBlockValue).prod) = 186461254597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_463
      · exact prime_oneHundredThirtyTwoDZ_491
      · exact prime_oneHundredThirtyTwoDZ_68351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 186461254597) ^ 93230627298 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 62153751532 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 402724092 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 379758156 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 2727996 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_191145530867 : Nat.Prime 191145530867 := by
  apply lucas_primality 191145530867 (2 : ZMod 191145530867)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (1423, 1), (754639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (1423, 1), (754639, 1)] : List FactorBlock).map factorBlockValue).prod) = 191145530867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_89
      · exact prime_oneHundredThirtyTwoDZ_1423
      · exact prime_oneHundredThirtyTwoDZ_754639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 191145530867) ^ 95572765433 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 191145530867) ^ 2147702594 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 191145530867) ^ 134325742 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 191145530867) ^ 253294 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_195355506911 : Nat.Prime 195355506911 := by
  apply lucas_primality 195355506911 (11 : ZMod 195355506911)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1009, 1), (667631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1009, 1), (667631, 1)] : List FactorBlock).map factorBlockValue).prod) = 195355506911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_29
      · exact prime_oneHundredThirtyTwoDZ_1009
      · exact prime_oneHundredThirtyTwoDZ_667631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 195355506911) ^ 97677753455 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 195355506911) ^ 39071101382 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 195355506911) ^ 6736396790 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 195355506911) ^ 193612990 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 195355506911) ^ 292610 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_202459380199 : Nat.Prime 202459380199 := by
  apply lucas_primality 202459380199 (15 : ZMod 202459380199)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (503630299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (503630299, 1)] : List FactorBlock).map factorBlockValue).prod) = 202459380199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_67
      · exact prime_oneHundredThirtyTwoDZ_503630299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 202459380199) ^ 101229690099 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (15 : ZMod 202459380199) ^ 67486460066 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (15 : ZMod 202459380199) ^ 3021781794 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (15 : ZMod 202459380199) ^ 402 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_210359508407 : Nat.Prime 210359508407 := by
  apply lucas_primality 210359508407 (5 : ZMod 210359508407)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (859, 1), (6444443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (859, 1), (6444443, 1)] : List FactorBlock).map factorBlockValue).prod) = 210359508407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_19
      · exact prime_oneHundredThirtyTwoDZ_859
      · exact prime_oneHundredThirtyTwoDZ_6444443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 210359508407) ^ 105179754203 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 210359508407) ^ 11071553074 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 210359508407) ^ 244888834 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 210359508407) ^ 32642 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_19
      · exact prime_oneHundredThirtyTwoDZ_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_413895224417 : Nat.Prime 413895224417 := by
  apply lucas_primality 413895224417 (3 : ZMod 413895224417)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (12934225763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (12934225763, 1)] : List FactorBlock).map factorBlockValue).prod) = 413895224417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_12934225763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 413895224417) ^ 206947612208 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 413895224417) ^ 32 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_467334340387 : Nat.Prime 467334340387 := by
  apply lucas_primality 467334340387 (2 : ZMod 467334340387)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (47, 1), (40419853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (47, 1), (40419853, 1)] : List FactorBlock).map factorBlockValue).prod) = 467334340387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_41
      · exact prime_oneHundredThirtyTwoDZ_47
      · exact prime_oneHundredThirtyTwoDZ_40419853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 467334340387) ^ 233667170193 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 467334340387) ^ 155778113462 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 467334340387) ^ 11398398546 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 467334340387) ^ 9943283838 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 467334340387) ^ 11562 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_476907466417 : Nat.Prime 476907466417 := by
  apply lucas_primality 476907466417 (10 : ZMod 476907466417)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) = 476907466417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_43
      · exact prime_oneHundredThirtyTwoDZ_73
      · exact prime_oneHundredThirtyTwoDZ_3165203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 476907466417) ^ 238453733208 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 158969155472 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 11090871312 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 6532978992 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 150672 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_526815301981 : Nat.Prime 526815301981 := by
  apply lucas_primality 526815301981 (2 : ZMod 526815301981)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (1321, 1), (604243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (1321, 1), (604243, 1)] : List FactorBlock).map factorBlockValue).prod) = 526815301981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_1321
      · exact prime_oneHundredThirtyTwoDZ_604243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 526815301981) ^ 263407650990 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 526815301981) ^ 175605100660 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 526815301981) ^ 105363060396 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 526815301981) ^ 47892300180 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 526815301981) ^ 398800380 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 526815301981) ^ 871860 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_538664062567 : Nat.Prime 538664062567 := by
  apply lucas_primality 538664062567 (3 : ZMod 538664062567)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (877, 1), (298451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (877, 1), (298451, 1)] : List FactorBlock).map factorBlockValue).prod) = 538664062567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_877
      · exact prime_oneHundredThirtyTwoDZ_298451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 538664062567) ^ 269332031283 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 538664062567) ^ 179554687522 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 538664062567) ^ 76952008938 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 538664062567) ^ 614212158 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 538664062567) ^ 1804866 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_543712374719 : Nat.Prime 543712374719 := by
  apply lucas_primality 543712374719 (13 : ZMod 543712374719)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (11819834233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (11819834233, 1)] : List FactorBlock).map factorBlockValue).prod) = 543712374719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_23
      · exact prime_oneHundredThirtyTwoDZ_11819834233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 543712374719) ^ 271856187359 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 543712374719) ^ 23639668466 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 543712374719) ^ 46 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_583527732737 : Nat.Prime 583527732737 := by
  apply lucas_primality 583527732737 (3 : ZMod 583527732737)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (13, 1), (2803, 1), (31277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (13, 1), (2803, 1), (31277, 1)] : List FactorBlock).map factorBlockValue).prod) = 583527732737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_2803
      · exact prime_oneHundredThirtyTwoDZ_31277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 583527732737) ^ 291763866368 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 583527732737) ^ 44886748672 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 583527732737) ^ 208179712 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 583527732737) ^ 18656768 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_700722673081 : Nat.Prime 700722673081 := by
  apply lucas_primality 700722673081 (13 : ZMod 700722673081)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (5839355609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (5839355609, 1)] : List FactorBlock).map factorBlockValue).prod) = 700722673081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_5839355609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 700722673081) ^ 350361336540 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 700722673081) ^ 233574224360 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 700722673081) ^ 140144534616 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 700722673081) ^ 120 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_749523766273 : Nat.Prime 749523766273 := by
  apply lucas_primality 749523766273 (5 : ZMod 749523766273)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) = 749523766273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_47
      · exact prime_oneHundredThirtyTwoDZ_821
      · exact prime_oneHundredThirtyTwoDZ_6323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 749523766273) ^ 374761883136 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 249841255424 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 15947314176 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 912940032 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 118539264 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_792913289053 : Nat.Prime 792913289053 := by
  apply lucas_primality 792913289053 (5 : ZMod 792913289053)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (66076107421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (66076107421, 1)] : List FactorBlock).map factorBlockValue).prod) = 792913289053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_66076107421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 792913289053) ^ 396456644526 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 792913289053) ^ 264304429684 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 792913289053) ^ 12 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_890872725739 : Nat.Prime 890872725739 := by
  apply lucas_primality 890872725739 (2 : ZMod 890872725739)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (557, 1), (6199273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (557, 1), (6199273, 1)] : List FactorBlock).map factorBlockValue).prod) = 890872725739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_43
      · exact prime_oneHundredThirtyTwoDZ_557
      · exact prime_oneHundredThirtyTwoDZ_6199273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 890872725739) ^ 445436362869 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 890872725739) ^ 296957575246 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 890872725739) ^ 20717970366 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 890872725739) ^ 1599412434 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 890872725739) ^ 143706 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_909713258563 : Nat.Prime 909713258563 := by
  apply lucas_primality 909713258563 (2 : ZMod 909713258563)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (47, 1), (263, 1), (331511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (47, 1), (263, 1), (331511, 1)] : List FactorBlock).map factorBlockValue).prod) = 909713258563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_37
      · exact prime_oneHundredThirtyTwoDZ_47
      · exact prime_oneHundredThirtyTwoDZ_263
      · exact prime_oneHundredThirtyTwoDZ_331511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 909713258563) ^ 454856629281 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 909713258563) ^ 303237752854 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 909713258563) ^ 24586844826 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 909713258563) ^ 19355601246 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 909713258563) ^ 3458985774 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 909713258563) ^ 2744142 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1295508299753 : Nat.Prime 1295508299753 := by
  apply lucas_primality 1295508299753 (3 : ZMod 1295508299753)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1295508299753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_43759
      · exact prime_oneHundredThirtyTwoDZ_3700691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1295508299753) ^ 647754149876 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 29605528 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 350072 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1334656385269 : Nat.Prime 1334656385269 := by
  apply lucas_primality 1334656385269 (2 : ZMod 1334656385269)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (541, 1), (205584779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (541, 1), (205584779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1334656385269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_541
      · exact prime_oneHundredThirtyTwoDZ_205584779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1334656385269) ^ 667328192634 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1334656385269) ^ 444885461756 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1334656385269) ^ 2467017348 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1334656385269) ^ 6492 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1408055893883 : Nat.Prime 1408055893883 := by
  apply lucas_primality 1408055893883 (5 : ZMod 1408055893883)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (64002540631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (64002540631, 1)] : List FactorBlock).map factorBlockValue).prod) = 1408055893883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_64002540631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1408055893883) ^ 704027946941 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1408055893883) ^ 128005081262 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1408055893883) ^ 22 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1408520993987 : Nat.Prime 1408520993987 := by
  apply lucas_primality 1408520993987 (2 : ZMod 1408520993987)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (109, 1), (340058183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (109, 1), (340058183, 1)] : List FactorBlock).map factorBlockValue).prod) = 1408520993987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_19
      · exact prime_oneHundredThirtyTwoDZ_109
      · exact prime_oneHundredThirtyTwoDZ_340058183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1408520993987) ^ 704260496993 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1408520993987) ^ 74132683894 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1408520993987) ^ 12922210954 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1408520993987) ^ 4142 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1477220469691 : Nat.Prime 1477220469691 := by
  apply lucas_primality 1477220469691 (7 : ZMod 1477220469691)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1171, 1), (6007159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1171, 1), (6007159, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477220469691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_1171
      · exact prime_oneHundredThirtyTwoDZ_6007159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1477220469691) ^ 738610234845 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1477220469691) ^ 492406823230 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1477220469691) ^ 295444093938 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1477220469691) ^ 211031495670 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1477220469691) ^ 1261503390 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1477220469691) ^ 245910 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1651106141567 : Nat.Prime 1651106141567 := by
  apply lucas_primality 1651106141567 (5 : ZMod 1651106141567)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (52639, 1), (2240471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (52639, 1), (2240471, 1)] : List FactorBlock).map factorBlockValue).prod) = 1651106141567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_52639
      · exact prime_oneHundredThirtyTwoDZ_2240471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1651106141567) ^ 825553070783 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1651106141567) ^ 235872305938 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1651106141567) ^ 31366594 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1651106141567) ^ 736946 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2181045234779 : Nat.Prime 2181045234779 := by
  apply lucas_primality 2181045234779 (2 : ZMod 2181045234779)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (23, 1), (2495475097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (23, 1), (2495475097, 1)] : List FactorBlock).map factorBlockValue).prod) = 2181045234779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_19
      · exact prime_oneHundredThirtyTwoDZ_23
      · exact prime_oneHundredThirtyTwoDZ_2495475097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2181045234779) ^ 1090522617389 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2181045234779) ^ 114791854462 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2181045234779) ^ 94828053686 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2181045234779) ^ 874 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2291465917703 : Nat.Prime 2291465917703 := by
  apply lucas_primality 2291465917703 (5 : ZMod 2291465917703)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (131, 1), (433, 1), (91397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (131, 1), (433, 1), (91397, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291465917703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_131
      · exact prime_oneHundredThirtyTwoDZ_433
      · exact prime_oneHundredThirtyTwoDZ_91397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2291465917703) ^ 1145732958851 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2291465917703) ^ 176266609054 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2291465917703) ^ 134792112806 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2291465917703) ^ 17492106242 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2291465917703) ^ 5292069094 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2291465917703) ^ 25071566 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2337384356897 : Nat.Prime 2337384356897 := by
  apply lucas_primality 2337384356897 (3 : ZMod 2337384356897)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (83, 1), (263, 1), (3346157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (83, 1), (263, 1), (3346157, 1)] : List FactorBlock).map factorBlockValue).prod) = 2337384356897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_83
      · exact prime_oneHundredThirtyTwoDZ_263
      · exact prime_oneHundredThirtyTwoDZ_3346157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2337384356897) ^ 1168692178448 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2337384356897) ^ 28161257312 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2337384356897) ^ 8887392992 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2337384356897) ^ 698528 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2517652494991 : Nat.Prime 2517652494991 := by
  apply lucas_primality 2517652494991 (3 : ZMod 2517652494991)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (107, 1), (4993, 1), (52361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (107, 1), (4993, 1), (52361, 1)] : List FactorBlock).map factorBlockValue).prod) = 2517652494991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_107
      · exact prime_oneHundredThirtyTwoDZ_4993
      · exact prime_oneHundredThirtyTwoDZ_52361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2517652494991) ^ 1258826247495 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 839217498330 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 503530498998 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 23529462570 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 504236430 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 48082590 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2565239310373 : Nat.Prime 2565239310373 := by
  apply lucas_primality 2565239310373 (2 : ZMod 2565239310373)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (179, 1), (3407, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (179, 1), (3407, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) = 2565239310373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_71
      · exact prime_oneHundredThirtyTwoDZ_179
      · exact prime_oneHundredThirtyTwoDZ_3407
      · exact prime_oneHundredThirtyTwoDZ_4937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2565239310373) ^ 1282619655186 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2565239310373) ^ 855079770124 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2565239310373) ^ 36130131132 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2565239310373) ^ 14330945868 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2565239310373) ^ 752931996 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2565239310373) ^ 519594756 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2635260597413 : Nat.Prime 2635260597413 := by
  apply lucas_primality 2635260597413 (2 : ZMod 2635260597413)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (509, 1), (1294332317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (509, 1), (1294332317, 1)] : List FactorBlock).map factorBlockValue).prod) = 2635260597413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_509
      · exact prime_oneHundredThirtyTwoDZ_1294332317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2635260597413) ^ 1317630298706 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2635260597413) ^ 5177329268 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2635260597413) ^ 2036 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2761161230591 : Nat.Prime 2761161230591 := by
  apply lucas_primality 2761161230591 (7 : ZMod 2761161230591)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (82193, 1), (479909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (82193, 1), (479909, 1)] : List FactorBlock).map factorBlockValue).prod) = 2761161230591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_82193
      · exact prime_oneHundredThirtyTwoDZ_479909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2761161230591) ^ 1380580615295 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2761161230591) ^ 552232246118 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2761161230591) ^ 394451604370 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2761161230591) ^ 33593630 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 2761161230591) ^ 5753510 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2786044081081 : Nat.Prime 2786044081081 := by
  apply lucas_primality 2786044081081 (11 : ZMod 2786044081081)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (47, 2), (59, 1), (71, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (47, 2), (59, 1), (71, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2786044081081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_47
      · exact prime_oneHundredThirtyTwoDZ_59
      · exact prime_oneHundredThirtyTwoDZ_71
      · exact prime_oneHundredThirtyTwoDZ_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2786044081081) ^ 1393022040540 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 928681360360 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 557208816216 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 214311083160 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 59277533640 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 47221086120 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 39240057480 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 14435461560 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2860024003019 : Nat.Prime 2860024003019 := by
  apply lucas_primality 2860024003019 (6 : ZMod 2860024003019)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (59, 1), (266346061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (59, 1), (266346061, 1)] : List FactorBlock).map factorBlockValue).prod) = 2860024003019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_59
      · exact prime_oneHundredThirtyTwoDZ_266346061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2860024003019) ^ 1430012001509 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2860024003019) ^ 408574857574 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2860024003019) ^ 220001846386 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2860024003019) ^ 48474983102 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2860024003019) ^ 10738 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_3039854166347 : Nat.Prime 3039854166347 := by
  apply lucas_primality 3039854166347 (2 : ZMod 3039854166347)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (7875269861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (7875269861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3039854166347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_193
      · exact prime_oneHundredThirtyTwoDZ_7875269861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3039854166347) ^ 1519927083173 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3039854166347) ^ 15750539722 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3039854166347) ^ 386 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_4014078193691 : Nat.Prime 4014078193691 := by
  apply lucas_primality 4014078193691 (2 : ZMod 4014078193691)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) = 4014078193691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_829
      · exact prime_oneHundredThirtyTwoDZ_1051
      · exact prime_oneHundredThirtyTwoDZ_460711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4014078193691) ^ 2007039096845 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 802815638738 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 4842072610 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 3819294190 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 8712790 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_4103423718869 : Nat.Prime 4103423718869 := by
  apply lucas_primality 4103423718869 (2 : ZMod 4103423718869)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (233, 1), (7019, 1), (627271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (233, 1), (7019, 1), (627271, 1)] : List FactorBlock).map factorBlockValue).prod) = 4103423718869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_233
      · exact prime_oneHundredThirtyTwoDZ_7019
      · exact prime_oneHundredThirtyTwoDZ_627271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4103423718869) ^ 2051711859434 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103423718869) ^ 17611260596 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103423718869) ^ 584616572 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103423718869) ^ 6541708 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_4146355325719 : Nat.Prime 4146355325719 := by
  apply lucas_primality 4146355325719 (3 : ZMod 4146355325719)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 2), (1223, 1), (651733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 2), (1223, 1), (651733, 1)] : List FactorBlock).map factorBlockValue).prod) = 4146355325719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_1223
      · exact prime_oneHundredThirtyTwoDZ_651733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4146355325719) ^ 2073177662859 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4146355325719) ^ 1382118441906 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4146355325719) ^ 243903254454 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4146355325719) ^ 3390315066 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4146355325719) ^ 6362046 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_4332477976933 : Nat.Prime 4332477976933 := by
  apply lucas_primality 4332477976933 (2 : ZMod 4332477976933)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (29, 1), (151, 1), (3049, 1), (3863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (29, 1), (151, 1), (3049, 1), (3863, 1)] : List FactorBlock).map factorBlockValue).prod) = 4332477976933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_29
      · exact prime_oneHundredThirtyTwoDZ_151
      · exact prime_oneHundredThirtyTwoDZ_3049
      · exact prime_oneHundredThirtyTwoDZ_3863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4332477976933) ^ 2166238988466 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4332477976933) ^ 1444159325644 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4332477976933) ^ 618925425276 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4332477976933) ^ 149395792308 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4332477976933) ^ 28691907132 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4332477976933) ^ 1420950468 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4332477976933) ^ 1121531964 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_4359340868263 : Nat.Prime 4359340868263 := by
  apply lucas_primality 4359340868263 (3 : ZMod 4359340868263)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (9196921663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (9196921663, 1)] : List FactorBlock).map factorBlockValue).prod) = 4359340868263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_79
      · exact prime_oneHundredThirtyTwoDZ_9196921663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4359340868263) ^ 2179670434131 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4359340868263) ^ 1453113622754 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4359340868263) ^ 55181529978 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4359340868263) ^ 474 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_4443632232239 : Nat.Prime 4443632232239 := by
  apply lucas_primality 4443632232239 (7 : ZMod 4443632232239)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4243, 1), (523642733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4243, 1), (523642733, 1)] : List FactorBlock).map factorBlockValue).prod) = 4443632232239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_4243
      · exact prime_oneHundredThirtyTwoDZ_523642733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4443632232239) ^ 2221816116119 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 4443632232239) ^ 1047285466 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 4443632232239) ^ 8486 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_4624461037321 : Nat.Prime 4624461037321 := by
  apply lucas_primality 4624461037321 (13 : ZMod 4624461037321)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (83, 1), (457, 1), (1015981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (83, 1), (457, 1), (1015981, 1)] : List FactorBlock).map factorBlockValue).prod) = 4624461037321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_83
      · exact prime_oneHundredThirtyTwoDZ_457
      · exact prime_oneHundredThirtyTwoDZ_1015981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 4624461037321) ^ 2312230518660 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 4624461037321) ^ 1541487012440 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 4624461037321) ^ 924892207464 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 4624461037321) ^ 55716398040 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 4624461037321) ^ 10119170760 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 4624461037321) ^ 4551720 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_5515691096141 : Nat.Prime 5515691096141 := by
  apply lucas_primality 5515691096141 (3 : ZMod 5515691096141)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (89, 1), (379, 1), (480941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (89, 1), (379, 1), (480941, 1)] : List FactorBlock).map factorBlockValue).prod) = 5515691096141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_89
      · exact prime_oneHundredThirtyTwoDZ_379
      · exact prime_oneHundredThirtyTwoDZ_480941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5515691096141) ^ 2757845548070 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5515691096141) ^ 1103138219228 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5515691096141) ^ 324452417420 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5515691096141) ^ 61974057260 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5515691096141) ^ 14553274660 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5515691096141) ^ 11468540 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_5623554424127 : Nat.Prime 5623554424127 := by
  apply lucas_primality 5623554424127 (5 : ZMod 5623554424127)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (367, 1), (7661518289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (367, 1), (7661518289, 1)] : List FactorBlock).map factorBlockValue).prod) = 5623554424127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_367
      · exact prime_oneHundredThirtyTwoDZ_7661518289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5623554424127) ^ 2811777212063 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5623554424127) ^ 15323036578 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5623554424127) ^ 734 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_5753678878657 : Nat.Prime 5753678878657 := by
  apply lucas_primality 5753678878657 (7 : ZMod 5753678878657)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (4987, 1), (222557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (4987, 1), (222557, 1)] : List FactorBlock).map factorBlockValue).prod) = 5753678878657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_4987
      · exact prime_oneHundredThirtyTwoDZ_222557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5753678878657) ^ 2876839439328 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5753678878657) ^ 1917892959552 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5753678878657) ^ 1153735488 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5753678878657) ^ 25852608 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_7929132890531 : Nat.Prime 7929132890531 := by
  apply lucas_primality 7929132890531 (2 : ZMod 7929132890531)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (792913289053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (792913289053, 1)] : List FactorBlock).map factorBlockValue).prod) = 7929132890531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_792913289053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7929132890531) ^ 3964566445265 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7929132890531) ^ 1585826578106 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7929132890531) ^ 10 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_9231195796909 : Nat.Prime 9231195796909 := by
  apply lucas_primality 9231195796909 (2 : ZMod 9231195796909)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (33446361583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (33446361583, 1)] : List FactorBlock).map factorBlockValue).prod) = 9231195796909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_23
      · exact prime_oneHundredThirtyTwoDZ_33446361583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9231195796909) ^ 4615597898454 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231195796909) ^ 3077065265636 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231195796909) ^ 401356338996 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231195796909) ^ 276 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_13971226936099 : Nat.Prime 13971226936099 := by
  apply lucas_primality 13971226936099 (2 : ZMod 13971226936099)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13971226936099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_21617
      · exact prime_oneHundredThirtyTwoDZ_6336347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13971226936099) ^ 6985613468049 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 4657075645366 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 821836878594 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 646307394 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 2204934 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_15858265781063 : Nat.Prime 15858265781063 := by
  apply lucas_primality 15858265781063 (5 : ZMod 15858265781063)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7929132890531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7929132890531, 1)] : List FactorBlock).map factorBlockValue).prod) = 15858265781063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7929132890531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 15858265781063) ^ 7929132890531 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 15858265781063) ^ 2 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_16731589050991 : Nat.Prime 16731589050991 := by
  apply lucas_primality 16731589050991 (23 : ZMod 16731589050991)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (5, 1), (11, 1), (547, 1), (381443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (5, 1), (11, 1), (547, 1), (381443, 1)] : List FactorBlock).map factorBlockValue).prod) = 16731589050991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_547
      · exact prime_oneHundredThirtyTwoDZ_381443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 16731589050991) ^ 8365794525495 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 16731589050991) ^ 5577196350330 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 16731589050991) ^ 3346317810198 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 16731589050991) ^ 1521053550090 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 16731589050991) ^ 30587914170 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 16731589050991) ^ 43863930 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_17491261576223 : Nat.Prime 17491261576223 := by
  apply lucas_primality 17491261576223 (5 : ZMod 17491261576223)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (229, 1), (599, 1), (479377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (229, 1), (599, 1), (479377, 1)] : List FactorBlock).map factorBlockValue).prod) = 17491261576223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_19
      · exact prime_oneHundredThirtyTwoDZ_229
      · exact prime_oneHundredThirtyTwoDZ_599
      · exact prime_oneHundredThirtyTwoDZ_479377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17491261576223) ^ 8745630788111 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 17491261576223) ^ 2498751653746 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 17491261576223) ^ 920592714538 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 17491261576223) ^ 76381054918 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 17491261576223) ^ 29200770578 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 17491261576223) ^ 36487486 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_19104580532281 : Nat.Prime 19104580532281 := by
  apply lucas_primality 19104580532281 (19 : ZMod 19104580532281)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (79, 1), (7993, 1), (14831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (79, 1), (7993, 1), (14831, 1)] : List FactorBlock).map factorBlockValue).prod) = 19104580532281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_79
      · exact prime_oneHundredThirtyTwoDZ_7993
      · exact prime_oneHundredThirtyTwoDZ_14831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 19104580532281) ^ 9552290266140 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 6368193510760 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 3820916106456 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 1123798854840 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 241830133320 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 2390163960 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 1288151880 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_24474207549763 : Nat.Prime 24474207549763 := by
  apply lucas_primality 24474207549763 (3 : ZMod 24474207549763)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109, 1), (12474111901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109, 1), (12474111901, 1)] : List FactorBlock).map factorBlockValue).prod) = 24474207549763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_109
      · exact prime_oneHundredThirtyTwoDZ_12474111901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 24474207549763) ^ 12237103774881 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 24474207549763) ^ 8158069183254 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 24474207549763) ^ 224534014218 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 24474207549763) ^ 1962 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_26207436719791 : Nat.Prime 26207436719791 := by
  apply lucas_primality 26207436719791 (3 : ZMod 26207436719791)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (401, 1), (14629, 1), (49639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (401, 1), (14629, 1), (49639, 1)] : List FactorBlock).map factorBlockValue).prod) = 26207436719791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_401
      · exact prime_oneHundredThirtyTwoDZ_14629
      · exact prime_oneHundredThirtyTwoDZ_49639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26207436719791) ^ 13103718359895 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 26207436719791) ^ 8735812239930 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 26207436719791) ^ 5241487343958 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 26207436719791) ^ 65355203790 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 26207436719791) ^ 1791471510 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 26207436719791) ^ 527960610 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_28996602893813 : Nat.Prime 28996602893813 := by
  apply lucas_primality 28996602893813 (2 : ZMod 28996602893813)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (15461, 1), (468866873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (15461, 1), (468866873, 1)] : List FactorBlock).map factorBlockValue).prod) = 28996602893813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_15461
      · exact prime_oneHundredThirtyTwoDZ_468866873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28996602893813) ^ 14498301446906 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 28996602893813) ^ 1875467492 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 28996602893813) ^ 61844 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_33094146576847 : Nat.Prime 33094146576847 := by
  apply lucas_primality 33094146576847 (5 : ZMod 33094146576847)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5515691096141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5515691096141, 1)] : List FactorBlock).map factorBlockValue).prod) = 33094146576847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5515691096141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33094146576847) ^ 16547073288423 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 33094146576847) ^ 11031382192282 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 33094146576847) ^ 6 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_39877589675069 : Nat.Prime 39877589675069 := by
  apply lucas_primality 39877589675069 (2 : ZMod 39877589675069)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1847, 1), (2677, 1), (2016293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1847, 1), (2677, 1), (2016293, 1)] : List FactorBlock).map factorBlockValue).prod) = 39877589675069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_1847
      · exact prime_oneHundredThirtyTwoDZ_2677
      · exact prime_oneHundredThirtyTwoDZ_2016293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39877589675069) ^ 19938794837534 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 39877589675069) ^ 21590465444 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 39877589675069) ^ 14896372684 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 39877589675069) ^ 19777676 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_47
      · exact prime_oneHundredThirtyTwoDZ_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_66139999399751 : Nat.Prime 66139999399751 := by
  apply lucas_primality 66139999399751 (7 : ZMod 66139999399751)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) = 66139999399751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_1321
      · exact prime_oneHundredThirtyTwoDZ_200272519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 66139999399751) ^ 33069999699875 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 13227999879950 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 50068129750 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 330250 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_103388670991363 : Nat.Prime 103388670991363 := by
  apply lucas_primality 103388670991363 (2 : ZMod 103388670991363)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (201101, 1), (758279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (201101, 1), (758279, 1)] : List FactorBlock).map factorBlockValue).prod) = 103388670991363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_113
      · exact prime_oneHundredThirtyTwoDZ_201101
      · exact prime_oneHundredThirtyTwoDZ_758279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 103388670991363) ^ 51694335495681 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 103388670991363) ^ 34462890330454 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 103388670991363) ^ 914943991074 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 103388670991363) ^ 514113162 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 103388670991363) ^ 136346478 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_130417135331503 : Nat.Prime 130417135331503 := by
  apply lucas_primality 130417135331503 (3 : ZMod 130417135331503)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) = 130417135331503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_29
      · exact prime_oneHundredThirtyTwoDZ_749523766273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 130417135331503) ^ 65208567665751 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 43472378443834 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 4497142597638 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 174 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_146845245298579 : Nat.Prime 146845245298579 := by
  apply lucas_primality 146845245298579 (2 : ZMod 146845245298579)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (24474207549763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (24474207549763, 1)] : List FactorBlock).map factorBlockValue).prod) = 146845245298579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_24474207549763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 146845245298579) ^ 73422622649289 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 146845245298579) ^ 48948415099526 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 146845245298579) ^ 6 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_159437749709561 : Nat.Prime 159437749709561 := by
  apply lucas_primality 159437749709561 (6 : ZMod 159437749709561)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (59, 1), (9651195503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (59, 1), (9651195503, 1)] : List FactorBlock).map factorBlockValue).prod) = 159437749709561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_59
      · exact prime_oneHundredThirtyTwoDZ_9651195503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 159437749709561) ^ 79718874854780 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 159437749709561) ^ 31887549941912 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 159437749709561) ^ 22776821387080 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 159437749709561) ^ 2702334740840 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 159437749709561) ^ 16520 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_201243445356743 : Nat.Prime 201243445356743 := by
  apply lucas_primality 201243445356743 (5 : ZMod 201243445356743)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (526815301981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (526815301981, 1)] : List FactorBlock).map factorBlockValue).prod) = 201243445356743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_191
      · exact prime_oneHundredThirtyTwoDZ_526815301981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 201243445356743) ^ 100621722678371 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 201243445356743) ^ 1053630603962 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 201243445356743) ^ 382 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_221173209466147 : Nat.Prime 221173209466147 := by
  apply lucas_primality 221173209466147 (2 : ZMod 221173209466147)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (2131, 1), (274572647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (2131, 1), (274572647, 1)] : List FactorBlock).map factorBlockValue).prod) = 221173209466147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_2131
      · exact prime_oneHundredThirtyTwoDZ_274572647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 221173209466147) ^ 110586604733073 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 221173209466147) ^ 73724403155382 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 221173209466147) ^ 31596172780878 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 221173209466147) ^ 103788460566 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 221173209466147) ^ 805518 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_240844691621461 : Nat.Prime 240844691621461 := by
  apply lucas_primality 240844691621461 (2 : ZMod 240844691621461)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) = 240844691621461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_4014078193691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240844691621461) ^ 120422345810730 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 80281563873820 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 48168938324292 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 60 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_10789
      · exact prime_oneHundredThirtyTwoDZ_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_402486890713487 : Nat.Prime 402486890713487 := by
  apply lucas_primality 402486890713487 (5 : ZMod 402486890713487)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (201243445356743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (201243445356743, 1)] : List FactorBlock).map factorBlockValue).prod) = 402486890713487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_201243445356743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 402486890713487) ^ 201243445356743 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 402486890713487) ^ 2 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_439099334161333 : Nat.Prime 439099334161333 := by
  apply lucas_primality 439099334161333 (2 : ZMod 439099334161333)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (239, 1), (35603, 1), (330791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (239, 1), (35603, 1), (330791, 1)] : List FactorBlock).map factorBlockValue).prod) = 439099334161333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_239
      · exact prime_oneHundredThirtyTwoDZ_35603
      · exact prime_oneHundredThirtyTwoDZ_330791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 439099334161333) ^ 219549667080666 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 439099334161333) ^ 146366444720444 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 439099334161333) ^ 33776871858564 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 439099334161333) ^ 1837235707788 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 439099334161333) ^ 12333211644 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 439099334161333) ^ 1327422252 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_458535343949863 : Nat.Prime 458535343949863 := by
  apply lucas_primality 458535343949863 (11 : ZMod 458535343949863)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (2635260597413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (2635260597413, 1)] : List FactorBlock).map factorBlockValue).prod) = 458535343949863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_29
      · exact prime_oneHundredThirtyTwoDZ_2635260597413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 458535343949863) ^ 229267671974931 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 458535343949863) ^ 152845114649954 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 458535343949863) ^ 15811563584478 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 458535343949863) ^ 174 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_507464504994017 : Nat.Prime 507464504994017 := by
  apply lucas_primality 507464504994017 (3 : ZMod 507464504994017)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (15858265781063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (15858265781063, 1)] : List FactorBlock).map factorBlockValue).prod) = 507464504994017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_15858265781063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 507464504994017) ^ 253732252497008 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 507464504994017) ^ 32 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_663817157358749 : Nat.Prime 663817157358749 := by
  apply lucas_primality 663817157358749 (2 : ZMod 663817157358749)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (2337384356897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (2337384356897, 1)] : List FactorBlock).map factorBlockValue).prod) = 663817157358749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_71
      · exact prime_oneHundredThirtyTwoDZ_2337384356897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 663817157358749) ^ 331908578679374 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 663817157358749) ^ 9349537427588 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 663817157358749) ^ 284 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_723857833738631 : Nat.Prime 723857833738631 := by
  apply lucas_primality 723857833738631 (7 : ZMod 723857833738631)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (113, 1), (153457, 1), (4174343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (113, 1), (153457, 1), (4174343, 1)] : List FactorBlock).map factorBlockValue).prod) = 723857833738631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_113
      · exact prime_oneHundredThirtyTwoDZ_153457
      · exact prime_oneHundredThirtyTwoDZ_4174343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 723857833738631) ^ 361928916869315 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 723857833738631) ^ 144771566747726 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 723857833738631) ^ 6405821537510 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 723857833738631) ^ 4717007590 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 723857833738631) ^ 173406410 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_893226076336441 : Nat.Prime 893226076336441 := by
  apply lucas_primality 893226076336441 (19 : ZMod 893226076336441)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 1), (11, 1), (347, 1), (30954047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 1), (11, 1), (347, 1), (30954047, 1)] : List FactorBlock).map factorBlockValue).prod) = 893226076336441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_347
      · exact prime_oneHundredThirtyTwoDZ_30954047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 893226076336441) ^ 446613038168220 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 893226076336441) ^ 297742025445480 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 893226076336441) ^ 178645215267288 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 893226076336441) ^ 127603725190920 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 893226076336441) ^ 81202370576040 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 893226076336441) ^ 2574138548520 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 893226076336441) ^ 28856520 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_998188812141893 : Nat.Prime 998188812141893 := by
  apply lucas_primality 998188812141893 (2 : ZMod 998188812141893)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (758111, 1), (47024249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (758111, 1), (47024249, 1)] : List FactorBlock).map factorBlockValue).prod) = 998188812141893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_758111
      · exact prime_oneHundredThirtyTwoDZ_47024249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 998188812141893) ^ 499094406070946 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 998188812141893) ^ 142598401734556 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 998188812141893) ^ 1316678972 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 998188812141893) ^ 21227108 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1308639295634981 : Nat.Prime 1308639295634981 := by
  apply lucas_primality 1308639295634981 (3 : ZMod 1308639295634981)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (5171, 1), (31699, 1), (399181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (5171, 1), (31699, 1), (399181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1308639295634981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_5171
      · exact prime_oneHundredThirtyTwoDZ_31699
      · exact prime_oneHundredThirtyTwoDZ_399181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1308639295634981) ^ 654319647817490 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1308639295634981) ^ 261727859126996 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1308639295634981) ^ 253072770380 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1308639295634981) ^ 41283299020 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1308639295634981) ^ 3278310580 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1362999438800939 : Nat.Prime 1362999438800939 := by
  apply lucas_primality 1362999438800939 (2 : ZMod 1362999438800939)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (606037, 1), (1124518337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (606037, 1), (1124518337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1362999438800939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_606037
      · exact prime_oneHundredThirtyTwoDZ_1124518337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1362999438800939) ^ 681499719400469 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1362999438800939) ^ 2249036674 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1362999438800939) ^ 1212074 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1368724432009199 : Nat.Prime 1368724432009199 := by
  apply lucas_primality 1368724432009199 (11 : ZMod 1368724432009199)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (71, 1), (97, 1), (4259, 1), (124769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (71, 1), (97, 1), (4259, 1), (124769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1368724432009199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_71
      · exact prime_oneHundredThirtyTwoDZ_97
      · exact prime_oneHundredThirtyTwoDZ_4259
      · exact prime_oneHundredThirtyTwoDZ_124769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1368724432009199) ^ 684362216004599 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 124429493819018 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 80513201882894 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 19277808901538 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 14110561154734 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 321372254522 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 10970068142 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1440831132044653 : Nat.Prime 1440831132044653 := by
  apply lucas_primality 1440831132044653 (2 : ZMod 1440831132044653)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (107, 1), (116089, 1), (9666227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (107, 1), (116089, 1), (9666227, 1)] : List FactorBlock).map factorBlockValue).prod) = 1440831132044653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_107
      · exact prime_oneHundredThirtyTwoDZ_116089
      · exact prime_oneHundredThirtyTwoDZ_9666227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1440831132044653) ^ 720415566022326 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1440831132044653) ^ 480277044014884 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1440831132044653) ^ 13465711514436 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1440831132044653) ^ 12411435468 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1440831132044653) ^ 149058276 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2357093374911809 : Nat.Prime 2357093374911809 := by
  apply lucas_primality 2357093374911809 (3 : ZMod 2357093374911809)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (47, 1), (60277551527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (47, 1), (60277551527, 1)] : List FactorBlock).map factorBlockValue).prod) = 2357093374911809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_47
      · exact prime_oneHundredThirtyTwoDZ_60277551527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2357093374911809) ^ 1178546687455904 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2357093374911809) ^ 181314874993216 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2357093374911809) ^ 50150922870464 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2357093374911809) ^ 39104 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_3224424695787569 : Nat.Prime 3224424695787569 := by
  apply lucas_primality 3224424695787569 (6 : ZMod 3224424695787569)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 1), (37, 1), (151, 1), (396380419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 1), (37, 1), (151, 1), (396380419, 1)] : List FactorBlock).map factorBlockValue).prod) = 3224424695787569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_37
      · exact prime_oneHundredThirtyTwoDZ_151
      · exact prime_oneHundredThirtyTwoDZ_396380419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3224424695787569) ^ 1612212347893784 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3224424695787569) ^ 460632099398224 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3224424695787569) ^ 248032668906736 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3224424695787569) ^ 87146613399664 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3224424695787569) ^ 21353805932368 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 3224424695787569) ^ 8134672 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_3524083610216669 : Nat.Prime 3524083610216669 := by
  apply lucas_primality 3524083610216669 (2 : ZMod 3524083610216669)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (401, 1), (14593, 1), (150555719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (401, 1), (14593, 1), (150555719, 1)] : List FactorBlock).map factorBlockValue).prod) = 3524083610216669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_401
      · exact prime_oneHundredThirtyTwoDZ_14593
      · exact prime_oneHundredThirtyTwoDZ_150555719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3524083610216669) ^ 1762041805108334 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3524083610216669) ^ 8788238429468 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3524083610216669) ^ 241491373276 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3524083610216669) ^ 23407172 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_4531774490983801 : Nat.Prime 4531774490983801 := by
  apply lucas_primality 4531774490983801 (7 : ZMod 4531774490983801)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (2517652494991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (2517652494991, 1)] : List FactorBlock).map factorBlockValue).prod) = 4531774490983801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_2517652494991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4531774490983801) ^ 2265887245491900 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 4531774490983801) ^ 1510591496994600 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 4531774490983801) ^ 906354898196760 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 4531774490983801) ^ 1800 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_5790862669909049 : Nat.Prime 5790862669909049 := by
  apply lucas_primality 5790862669909049 (3 : ZMod 5790862669909049)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (723857833738631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (723857833738631, 1)] : List FactorBlock).map factorBlockValue).prod) = 5790862669909049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_723857833738631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5790862669909049) ^ 2895431334954524 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 5790862669909049) ^ 8 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_6982819718723939 : Nat.Prime 6982819718723939 := by
  apply lucas_primality 6982819718723939 (2 : ZMod 6982819718723939)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6982819718723939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_79
      · exact prime_oneHundredThirtyTwoDZ_1583
      · exact prime_oneHundredThirtyTwoDZ_27918548017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6982819718723939) ^ 3491409859361969 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 88390123021822 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 4411130586686 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 250114 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_9659685377123689 : Nat.Prime 9659685377123689 := by
  apply lucas_primality 9659685377123689 (7 : ZMod 9659685377123689)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (402486890713487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (402486890713487, 1)] : List FactorBlock).map factorBlockValue).prod) = 9659685377123689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_402486890713487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 9659685377123689) ^ 4829842688561844 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 9659685377123689) ^ 3219895125707896 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 9659685377123689) ^ 24 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_17632332697524353 : Nat.Prime 17632332697524353 := by
  apply lucas_primality 17632332697524353 (3 : ZMod 17632332697524353)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (31, 1), (4443632232239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (31, 1), (4443632232239, 1)] : List FactorBlock).map factorBlockValue).prod) = 17632332697524353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_4443632232239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17632332697524353) ^ 8816166348762176 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 17632332697524353) ^ 568784925726592 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 17632332697524353) ^ 3968 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_19137506411674571 : Nat.Prime 19137506411674571 := by
  apply lucas_primality 19137506411674571 (6 : ZMod 19137506411674571)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (439, 1), (4359340868263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (439, 1), (4359340868263, 1)] : List FactorBlock).map factorBlockValue).prod) = 19137506411674571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_439
      · exact prime_oneHundredThirtyTwoDZ_4359340868263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 19137506411674571) ^ 9568753205837285 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 19137506411674571) ^ 3827501282334914 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 19137506411674571) ^ 43593408682630 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 19137506411674571) ^ 4390 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_20475120607168103 : Nat.Prime 20475120607168103 := by
  apply lucas_primality 20475120607168103 (5 : ZMod 20475120607168103)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (991, 1), (543712374719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (991, 1), (543712374719, 1)] : List FactorBlock).map factorBlockValue).prod) = 20475120607168103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_19
      · exact prime_oneHundredThirtyTwoDZ_991
      · exact prime_oneHundredThirtyTwoDZ_543712374719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20475120607168103) ^ 10237560303584051 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20475120607168103) ^ 1077637926693058 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20475120607168103) ^ 20661070239322 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20475120607168103) ^ 37658 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_30367193890285801 : Nat.Prime 30367193890285801 := by
  apply lucas_primality 30367193890285801 (11 : ZMod 30367193890285801)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 2), (5623554424127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 2), (5623554424127, 1)] : List FactorBlock).map factorBlockValue).prod) = 30367193890285801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_5623554424127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 30367193890285801) ^ 15183596945142900 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 30367193890285801) ^ 10122397963428600 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 30367193890285801) ^ 6073438778057160 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 30367193890285801) ^ 5400 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_41453814924485861 : Nat.Prime 41453814924485861 := by
  apply lucas_primality 41453814924485861 (3 : ZMod 41453814924485861)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (159437749709561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (159437749709561, 1)] : List FactorBlock).map factorBlockValue).prod) = 41453814924485861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_159437749709561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 41453814924485861) ^ 20726907462242930 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 41453814924485861) ^ 8290762984897172 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 41453814924485861) ^ 3188754994191220 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 41453814924485861) ^ 260 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_51807112427513579 : Nat.Prime 51807112427513579 := by
  apply lucas_primality 51807112427513579 (2 : ZMod 51807112427513579)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (893226076336441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (893226076336441, 1)] : List FactorBlock).map factorBlockValue).prod) = 51807112427513579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_29
      · exact prime_oneHundredThirtyTwoDZ_893226076336441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 51807112427513579) ^ 25903556213756789 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51807112427513579) ^ 1786452152672882 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 51807112427513579) ^ 58 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_78511797954027271 : Nat.Prime 78511797954027271 := by
  apply lucas_primality 78511797954027271 (3 : ZMod 78511797954027271)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) = 78511797954027271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_3457
      · exact prime_oneHundredThirtyTwoDZ_8263
      · exact prime_oneHundredThirtyTwoDZ_4362719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78511797954027271) ^ 39255898977013635 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 26170599318009090 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 15702359590805454 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 11215971136289610 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 22710962671110 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 9501609337290 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 17996070330 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_82907629848971723 : Nat.Prime 82907629848971723 := by
  apply lucas_primality 82907629848971723 (2 : ZMod 82907629848971723)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41453814924485861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41453814924485861, 1)] : List FactorBlock).map factorBlockValue).prod) = 82907629848971723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_41453814924485861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 82907629848971723) ^ 41453814924485861 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 82907629848971723) ^ 2 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_88604759030558453 : Nat.Prime 88604759030558453 := by
  apply lucas_primality 88604759030558453 (2 : ZMod 88604759030558453)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (83, 1), (1831, 1), (3643, 1), (3637297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (83, 1), (1831, 1), (3643, 1), (3637297, 1)] : List FactorBlock).map factorBlockValue).prod) = 88604759030558453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_83
      · exact prime_oneHundredThirtyTwoDZ_1831
      · exact prime_oneHundredThirtyTwoDZ_3643
      · exact prime_oneHundredThirtyTwoDZ_3637297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 88604759030558453) ^ 44302379515279226 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 88604759030558453) ^ 8054978093687132 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 88604759030558453) ^ 1067527217235644 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 88604759030558453) ^ 48391457690092 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 88604759030558453) ^ 24321921227164 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 88604759030558453) ^ 24360056116 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_182203163341714807 : Nat.Prime 182203163341714807 := by
  apply lucas_primality 182203163341714807 (3 : ZMod 182203163341714807)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (30367193890285801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (30367193890285801, 1)] : List FactorBlock).map factorBlockValue).prod) = 182203163341714807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_30367193890285801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 182203163341714807) ^ 91101581670857403 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 182203163341714807) ^ 60734387780571602 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 182203163341714807) ^ 6 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_186631761018299411 : Nat.Prime 186631761018299411 := by
  apply lucas_primality 186631761018299411 (10 : ZMod 186631761018299411)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (97, 1), (17491261576223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (97, 1), (17491261576223, 1)] : List FactorBlock).map factorBlockValue).prod) = 186631761018299411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_97
      · exact prime_oneHundredThirtyTwoDZ_17491261576223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 186631761018299411) ^ 93315880509149705 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 186631761018299411) ^ 37326352203659882 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 186631761018299411) ^ 16966523728936310 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 186631761018299411) ^ 1924038773384530 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 186631761018299411) ^ 10670 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_257138647306974463 : Nat.Prime 257138647306974463 := by
  apply lucas_primality 257138647306974463 (5 : ZMod 257138647306974463)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229841, 1), (186461254597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229841, 1), (186461254597, 1)] : List FactorBlock).map factorBlockValue).prod) = 257138647306974463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_229841
      · exact prime_oneHundredThirtyTwoDZ_186461254597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 257138647306974463) ^ 128569323653487231 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 257138647306974463) ^ 85712882435658154 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 257138647306974463) ^ 1118767527582 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 257138647306974463) ^ 1379046 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_272147314481131027 : Nat.Prime 272147314481131027 := by
  apply lucas_primality 272147314481131027 (2 : ZMod 272147314481131027)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (59, 1), (7772333, 1), (14130299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (59, 1), (7772333, 1), (14130299, 1)] : List FactorBlock).map factorBlockValue).prod) = 272147314481131027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_59
      · exact prime_oneHundredThirtyTwoDZ_7772333
      · exact prime_oneHundredThirtyTwoDZ_14130299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 272147314481131027) ^ 136073657240565513 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 272147314481131027) ^ 90715771493710342 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 272147314481131027) ^ 38878187783018718 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 272147314481131027) ^ 4612666347137814 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 272147314481131027) ^ 35014880922 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 272147314481131027) ^ 19259841174 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_476987026459955041 : Nat.Prime 476987026459955041 := by
  apply lucas_primality 476987026459955041 (11 : ZMod 476987026459955041)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 5), (5, 1), (41, 1), (2081, 1), (3391, 1), (42403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 5), (5, 1), (41, 1), (2081, 1), (3391, 1), (42403, 1)] : List FactorBlock).map factorBlockValue).prod) = 476987026459955041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_41
      · exact prime_oneHundredThirtyTwoDZ_2081
      · exact prime_oneHundredThirtyTwoDZ_3391
      · exact prime_oneHundredThirtyTwoDZ_42403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 476987026459955041) ^ 238493513229977520 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 476987026459955041) ^ 158995675486651680 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 476987026459955041) ^ 95397405291991008 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 476987026459955041) ^ 11633829913657440 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 476987026459955041) ^ 229210488447840 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 476987026459955041) ^ 140662644193440 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 476987026459955041) ^ 11248898107680 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_515381406101720317 : Nat.Prime 515381406101720317 := by
  apply lucas_primality 515381406101720317 (5 : ZMod 515381406101720317)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2903, 1), (9109, 1), (541387853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2903, 1), (9109, 1), (541387853, 1)] : List FactorBlock).map factorBlockValue).prod) = 515381406101720317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_2903
      · exact prime_oneHundredThirtyTwoDZ_9109
      · exact prime_oneHundredThirtyTwoDZ_541387853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 515381406101720317) ^ 257690703050860158 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 515381406101720317) ^ 171793802033906772 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 515381406101720317) ^ 177534070307172 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 515381406101720317) ^ 56579361741324 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 515381406101720317) ^ 951963372 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1109188763774599357 : Nat.Prime 1109188763774599357 := by
  apply lucas_primality 1109188763774599357 (5 : ZMod 1109188763774599357)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (89, 1), (199, 1), (29485457179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (89, 1), (199, 1), (29485457179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1109188763774599357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_59
      · exact prime_oneHundredThirtyTwoDZ_89
      · exact prime_oneHundredThirtyTwoDZ_199
      · exact prime_oneHundredThirtyTwoDZ_29485457179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1109188763774599357) ^ 554594381887299678 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 369729587924866452 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 18799809555501684 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 12462795098591004 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 5573812883289444 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 37618164 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1117685919860239201 : Nat.Prime 1117685919860239201 := by
  apply lucas_primality 1117685919860239201 (17 : ZMod 1117685919860239201)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (163, 1), (2447, 1), (1167580853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (163, 1), (2447, 1), (1167580853, 1)] : List FactorBlock).map factorBlockValue).prod) = 1117685919860239201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_163
      · exact prime_oneHundredThirtyTwoDZ_2447
      · exact prime_oneHundredThirtyTwoDZ_1167580853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1117685919860239201) ^ 558842959930119600 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (17 : ZMod 1117685919860239201) ^ 372561973286746400 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (17 : ZMod 1117685919860239201) ^ 223537183972047840 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (17 : ZMod 1117685919860239201) ^ 6856968833498400 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (17 : ZMod 1117685919860239201) ^ 456757629693600 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (17 : ZMod 1117685919860239201) ^ 957266400 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1135643102348768873 : Nat.Prime 1135643102348768873 := by
  apply lucas_primality 1135643102348768873 (3 : ZMod 1135643102348768873)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (47, 1), (73, 1), (1334656385269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (47, 1), (73, 1), (1334656385269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1135643102348768873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_47
      · exact prime_oneHundredThirtyTwoDZ_73
      · exact prime_oneHundredThirtyTwoDZ_1334656385269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1135643102348768873) ^ 567821551174384436 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1135643102348768873) ^ 36633648462863512 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1135643102348768873) ^ 24162619198909976 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1135643102348768873) ^ 15556754826695464 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1135643102348768873) ^ 850888 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1492065108799822793 : Nat.Prime 1492065108799822793 := by
  apply lucas_primality 1492065108799822793 (3 : ZMod 1492065108799822793)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1492065108799822793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_23
      · exact prime_oneHundredThirtyTwoDZ_47981
      · exact prime_oneHundredThirtyTwoDZ_88873
      · exact prime_oneHundredThirtyTwoDZ_1901651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1492065108799822793) ^ 746032554399911396 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 64872396034774904 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 31096998995432 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 16788733460104 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 784615635992 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2028232156090944157 : Nat.Prime 2028232156090944157 := by
  apply lucas_primality 2028232156090944157 (5 : ZMod 2028232156090944157)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (104033, 1), (324301, 1), (5009761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (104033, 1), (324301, 1), (5009761, 1)] : List FactorBlock).map factorBlockValue).prod) = 2028232156090944157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_104033
      · exact prime_oneHundredThirtyTwoDZ_324301
      · exact prime_oneHundredThirtyTwoDZ_5009761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2028232156090944157) ^ 1014116078045472078 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2028232156090944157) ^ 676077385363648052 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2028232156090944157) ^ 19496046024732 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2028232156090944157) ^ 6254165593356 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 2028232156090944157) ^ 404856071196 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2051946415555650209 : Nat.Prime 2051946415555650209 := by
  apply lucas_primality 2051946415555650209 (6 : ZMod 2051946415555650209)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (1308639295634981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (1308639295634981, 1)] : List FactorBlock).map factorBlockValue).prod) = 2051946415555650209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_1308639295634981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 2051946415555650209) ^ 1025973207777825104 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2051946415555650209) ^ 293135202222235744 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2051946415555650209) ^ 1568 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_101
      · exact prime_oneHundredThirtyTwoDZ_191
      · exact prime_oneHundredThirtyTwoDZ_48017
      · exact prime_oneHundredThirtyTwoDZ_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_3483026166924771923 : Nat.Prime 3483026166924771923 := by
  apply lucas_primality 3483026166924771923 (5 : ZMod 3483026166924771923)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (19137506411674571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (19137506411674571, 1)] : List FactorBlock).map factorBlockValue).prod) = 3483026166924771923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_19137506411674571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3483026166924771923) ^ 1741513083462385961 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3483026166924771923) ^ 497575166703538846 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3483026166924771923) ^ 267925089763443994 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 3483026166924771923) ^ 182 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_11176859198602392011 : Nat.Prime 11176859198602392011 := by
  apply lucas_primality 11176859198602392011 (2 : ZMod 11176859198602392011)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1117685919860239201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1117685919860239201, 1)] : List FactorBlock).map factorBlockValue).prod) = 11176859198602392011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_1117685919860239201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11176859198602392011) ^ 5588429599301196005 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11176859198602392011) ^ 2235371839720478402 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 11176859198602392011) ^ 10 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_13311937837557174217 : Nat.Prime 13311937837557174217 := by
  apply lucas_primality 13311937837557174217 (5 : ZMod 13311937837557174217)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) = 13311937837557174217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_4253
      · exact prime_oneHundredThirtyTwoDZ_130417135331503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13311937837557174217) ^ 6655968918778587108 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 4437312612519058072 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 3130011247956072 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 102072 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_19469144725157943457 : Nat.Prime 19469144725157943457 := by
  apply lucas_primality 19469144725157943457 (7 : ZMod 19469144725157943457)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (23, 1), (31, 1), (16731589050991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (23, 1), (31, 1), (16731589050991, 1)] : List FactorBlock).map factorBlockValue).prod) = 19469144725157943457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_23
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_16731589050991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 19469144725157943457) ^ 9734572362578971728 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 19469144725157943457) ^ 6489714908385981152 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 19469144725157943457) ^ 1145243807362231968 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 19469144725157943457) ^ 846484553267736672 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 19469144725157943457) ^ 628036926617998176 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 19469144725157943457) ^ 1163616 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_33140097923746668553 : Nat.Prime 33140097923746668553 := by
  apply lucas_primality 33140097923746668553 (11 : ZMod 33140097923746668553)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (1413233, 1), (108564107459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (1413233, 1), (108564107459, 1)] : List FactorBlock).map factorBlockValue).prod) = 33140097923746668553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_1413233
      · exact prime_oneHundredThirtyTwoDZ_108564107459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 33140097923746668553) ^ 16570048961873334276 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 33140097923746668553) ^ 11046699307915556184 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 33140097923746668553) ^ 23449847211144 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 33140097923746668553) ^ 305258328 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_43714142680393659277 : Nat.Prime 43714142680393659277 := by
  apply lucas_primality 43714142680393659277 (5 : ZMod 43714142680393659277)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (29, 1), (199, 1), (53551, 1), (357197261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (29, 1), (199, 1), (53551, 1), (357197261, 1)] : List FactorBlock).map factorBlockValue).prod) = 43714142680393659277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_29
      · exact prime_oneHundredThirtyTwoDZ_199
      · exact prime_oneHundredThirtyTwoDZ_53551
      · exact prime_oneHundredThirtyTwoDZ_357197261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 43714142680393659277) ^ 21857071340196829638 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 43714142680393659277) ^ 14571380893464553092 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 43714142680393659277) ^ 3974012970944878116 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 43714142680393659277) ^ 1507384230358402044 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 43714142680393659277) ^ 219669058695445524 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 43714142680393659277) ^ 816308615719476 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 43714142680393659277) ^ 122380957116 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_59249024358708502561 : Nat.Prime 59249024358708502561 := by
  apply lucas_primality 59249024358708502561 (14 : ZMod 59249024358708502561)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (11, 1), (84199277, 1), (133272001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (11, 1), (84199277, 1), (133272001, 1)] : List FactorBlock).map factorBlockValue).prod) = 59249024358708502561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_84199277
      · exact prime_oneHundredThirtyTwoDZ_133272001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 59249024358708502561) ^ 29624512179354251280 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (14 : ZMod 59249024358708502561) ^ 19749674786236167520 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (14 : ZMod 59249024358708502561) ^ 11849804871741700512 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (14 : ZMod 59249024358708502561) ^ 5386274941700772960 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (14 : ZMod 59249024358708502561) ^ 703676165280 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (14 : ZMod 59249024358708502561) ^ 444572182560 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_6863
      · exact prime_oneHundredThirtyTwoDZ_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_273845189866642875799 : Nat.Prime 273845189866642875799 := by
  apply lucas_primality 273845189866642875799 (13 : ZMod 273845189866642875799)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (310591, 1), (1651106141567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (310591, 1), (1651106141567, 1)] : List FactorBlock).map factorBlockValue).prod) = 273845189866642875799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_89
      · exact prime_oneHundredThirtyTwoDZ_310591
      · exact prime_oneHundredThirtyTwoDZ_1651106141567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 273845189866642875799) ^ 136922594933321437899 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 273845189866642875799) ^ 91281729955547625266 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 273845189866642875799) ^ 3076912245692616582 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 273845189866642875799) ^ 881690679596778 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (13 : ZMod 273845189866642875799) ^ 165855594 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_570311894838924320639 : Nat.Prime 570311894838924320639 := by
  apply lucas_primality 570311894838924320639 (7 : ZMod 570311894838924320639)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (956269, 1), (5815057, 1), (51280043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (956269, 1), (5815057, 1), (51280043, 1)] : List FactorBlock).map factorBlockValue).prod) = 570311894838924320639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_956269
      · exact prime_oneHundredThirtyTwoDZ_5815057
      · exact prime_oneHundredThirtyTwoDZ_51280043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 570311894838924320639) ^ 285155947419462160319 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 570311894838924320639) ^ 596392746014902 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 570311894838924320639) ^ 98075030879134 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 570311894838924320639) ^ 11121517484666 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_571466452238032796483 : Nat.Prime 571466452238032796483 := by
  apply lucas_primality 571466452238032796483 (2 : ZMod 571466452238032796483)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1531, 1), (186631761018299411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1531, 1), (186631761018299411, 1)] : List FactorBlock).map factorBlockValue).prod) = 571466452238032796483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_1531
      · exact prime_oneHundredThirtyTwoDZ_186631761018299411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 571466452238032796483) ^ 285733226119016398241 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 571466452238032796483) ^ 373263522036598822 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 571466452238032796483) ^ 3062 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_689580321364101784147 : Nat.Prime 689580321364101784147 := by
  apply lucas_primality 689580321364101784147 (2 : ZMod 689580321364101784147)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (223, 1), (515381406101720317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (223, 1), (515381406101720317, 1)] : List FactorBlock).map factorBlockValue).prod) = 689580321364101784147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_223
      · exact prime_oneHundredThirtyTwoDZ_515381406101720317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 689580321364101784147) ^ 344790160682050892073 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 689580321364101784147) ^ 229860107121367261382 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 689580321364101784147) ^ 3092288436610321902 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 689580321364101784147) ^ 1338 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_701170928896133910271 : Nat.Prime 701170928896133910271 := by
  apply lucas_primality 701170928896133910271 (3 : ZMod 701170928896133910271)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (476987026459955041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (476987026459955041, 1)] : List FactorBlock).map factorBlockValue).prod) = 701170928896133910271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_476987026459955041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 701170928896133910271) ^ 350585464448066955135 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 701170928896133910271) ^ 233723642965377970090 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 701170928896133910271) ^ 140234185779226782054 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 701170928896133910271) ^ 100167275556590558610 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 701170928896133910271) ^ 1470 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_813260164127262683411 : Nat.Prime 813260164127262683411 := by
  apply lucas_primality 813260164127262683411 (2 : ZMod 813260164127262683411)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (467119, 1), (4928953, 1), (35322163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (467119, 1), (4928953, 1), (35322163, 1)] : List FactorBlock).map factorBlockValue).prod) = 813260164127262683411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_467119
      · exact prime_oneHundredThirtyTwoDZ_4928953
      · exact prime_oneHundredThirtyTwoDZ_35322163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 813260164127262683411) ^ 406630082063631341705 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 813260164127262683411) ^ 162652032825452536682 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 813260164127262683411) ^ 1741012812853390 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 813260164127262683411) ^ 164996534583970 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 813260164127262683411) ^ 23024075964070 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1123485727816941907499 : Nat.Prime 1123485727816941907499 := by
  apply lucas_primality 1123485727816941907499 (2 : ZMod 1123485727816941907499)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (977, 1), (9931, 1), (11789, 1), (42557, 1), (115399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (977, 1), (9931, 1), (11789, 1), (42557, 1), (115399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1123485727816941907499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_977
      · exact prime_oneHundredThirtyTwoDZ_9931
      · exact prime_oneHundredThirtyTwoDZ_11789
      · exact prime_oneHundredThirtyTwoDZ_42557
      · exact prime_oneHundredThirtyTwoDZ_115399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1123485727816941907499) ^ 561742863908470953749 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123485727816941907499) ^ 1149934214756337674 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123485727816941907499) ^ 113129164013386558 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123485727816941907499) ^ 95299493410547282 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123485727816941907499) ^ 26399551843808114 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123485727816941907499) ^ 9735662595143302 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_23
      · exact prime_oneHundredThirtyTwoDZ_1549
      · exact prime_oneHundredThirtyTwoDZ_47713
      · exact prime_oneHundredThirtyTwoDZ_341461
      · exact prime_oneHundredThirtyTwoDZ_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1550411355806685423811 : Nat.Prime 1550411355806685423811 := by
  apply lucas_primality 1550411355806685423811 (2 : ZMod 1550411355806685423811)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1550411355806685423811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_3283807
      · exact prime_oneHundredThirtyTwoDZ_476907466417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1550411355806685423811) ^ 775205677903342711905 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 516803785268895141270 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 310082271161337084762 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 140946486891516856710 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 472138391752830 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 3250968930 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1566189032198506322689 : Nat.Prime 1566189032198506322689 := by
  apply lucas_primality 1566189032198506322689 (7 : ZMod 1566189032198506322689)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (211, 1), (5521, 1), (583527732737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (211, 1), (5521, 1), (583527732737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1566189032198506322689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_211
      · exact prime_oneHundredThirtyTwoDZ_5521
      · exact prime_oneHundredThirtyTwoDZ_583527732737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1566189032198506322689) ^ 783094516099253161344 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1566189032198506322689) ^ 522063010732835440896 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1566189032198506322689) ^ 7422696835064011008 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1566189032198506322689) ^ 283678506103696128 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1566189032198506322689) ^ 2684001024 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1626520328254525366823 : Nat.Prime 1626520328254525366823 := by
  apply lucas_primality 1626520328254525366823 (5 : ZMod 1626520328254525366823)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (813260164127262683411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (813260164127262683411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1626520328254525366823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_813260164127262683411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1626520328254525366823) ^ 813260164127262683411 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1626520328254525366823) ^ 2 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2271226716068239427359 : Nat.Prime 2271226716068239427359 := by
  apply lucas_primality 2271226716068239427359 (3 : ZMod 2271226716068239427359)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (31, 1), (541, 1), (3224424695787569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (31, 1), (541, 1), (3224424695787569, 1)] : List FactorBlock).map factorBlockValue).prod) = 2271226716068239427359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_541
      · exact prime_oneHundredThirtyTwoDZ_3224424695787569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2271226716068239427359) ^ 1135613358034119713679 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2271226716068239427359) ^ 757075572022746475786 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2271226716068239427359) ^ 324460959438319918194 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2271226716068239427359) ^ 73265377937685142818 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2271226716068239427359) ^ 4198200953915414838 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2271226716068239427359) ^ 704382 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_3455787998550372376649 : Nat.Prime 3455787998550372376649 := by
  apply lucas_primality 3455787998550372376649 (3 : ZMod 3455787998550372376649)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (93410561, 1), (4624461037321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (93410561, 1), (4624461037321, 1)] : List FactorBlock).map factorBlockValue).prod) = 3455787998550372376649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_93410561
      · exact prime_oneHundredThirtyTwoDZ_4624461037321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3455787998550372376649) ^ 1727893999275186188324 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3455787998550372376649) ^ 36995688298568 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3455787998550372376649) ^ 747284488 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_7602647635444694748803 : Nat.Prime 7602647635444694748803 := by
  apply lucas_primality 7602647635444694748803 (2 : ZMod 7602647635444694748803)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (399315911, 1), (413895224417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (399315911, 1), (413895224417, 1)] : List FactorBlock).map factorBlockValue).prod) = 7602647635444694748803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_23
      · exact prime_oneHundredThirtyTwoDZ_399315911
      · exact prime_oneHundredThirtyTwoDZ_413895224417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7602647635444694748803) ^ 3801323817722347374401 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7602647635444694748803) ^ 330549897193247597774 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7602647635444694748803) ^ 19039180323182 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7602647635444694748803) ^ 18368531906 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_34493952189981709766969 : Nat.Prime 34493952189981709766969 := by
  apply lucas_primality 34493952189981709766969 (3 : ZMod 34493952189981709766969)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (590489, 1), (663817157358749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (590489, 1), (663817157358749, 1)] : List FactorBlock).map factorBlockValue).prod) = 34493952189981709766969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_590489
      · exact prime_oneHundredThirtyTwoDZ_663817157358749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34493952189981709766969) ^ 17246976094990854883484 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 34493952189981709766969) ^ 3135813835452882706088 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 34493952189981709766969) ^ 58415909847569912 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 34493952189981709766969) ^ 51963032 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_35853529750253765128927 : Nat.Prime 35853529750253765128927 := by
  apply lucas_primality 35853529750253765128927 (3 : ZMod 35853529750253765128927)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853529750253765128927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_71
      · exact prime_oneHundredThirtyTwoDZ_8317
      · exact prime_oneHundredThirtyTwoDZ_66139999399751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853529750253765128927) ^ 17926764875126882564463 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 11951176583417921709642 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 2109031161779633242878 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 504979292257095283506 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 4310872880876970678 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 542085426 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_47886543588161587791203 : Nat.Prime 47886543588161587791203 := by
  apply lucas_primality 47886543588161587791203 (2 : ZMod 47886543588161587791203)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) = 47886543588161587791203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_14201963
      · exact prime_oneHundredThirtyTwoDZ_240844691621461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47886543588161587791203) ^ 23943271794080793895601 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 6840934798308798255886 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 3371825682700454 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 198827482 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_50418713460813862866463 : Nat.Prime 50418713460813862866463 := by
  apply lucas_primality 50418713460813862866463 (5 : ZMod 50418713460813862866463)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (17, 1), (74843, 1), (2159147, 1), (37763581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (17, 1), (74843, 1), (2159147, 1), (37763581, 1)] : List FactorBlock).map factorBlockValue).prod) = 50418713460813862866463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_74843
      · exact prime_oneHundredThirtyTwoDZ_2159147
      · exact prime_oneHundredThirtyTwoDZ_37763581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 50418713460813862866463) ^ 25209356730406931433231 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 50418713460813862866463) ^ 16806237820271287622154 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 50418713460813862866463) ^ 2965806674165521345086 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 50418713460813862866463) ^ 673659707131112634 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 50418713460813862866463) ^ 23351218541773146 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 50418713460813862866463) ^ 1335114735565302 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_54414165710388903315703 : Nat.Prime 54414165710388903315703 := by
  apply lucas_primality 54414165710388903315703 (7 : ZMod 54414165710388903315703)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (140689, 1), (55570169, 1), (89230949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (140689, 1), (55570169, 1), (89230949, 1)] : List FactorBlock).map factorBlockValue).prod) = 54414165710388903315703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_140689
      · exact prime_oneHundredThirtyTwoDZ_55570169
      · exact prime_oneHundredThirtyTwoDZ_89230949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 54414165710388903315703) ^ 27207082855194451657851 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 54414165710388903315703) ^ 18138055236796301105234 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 54414165710388903315703) ^ 4185705054645300255054 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 54414165710388903315703) ^ 386769155444909718 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 54414165710388903315703) ^ 979197412741158 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 54414165710388903315703) ^ 609812697502398 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_105310300298179943728621 : Nat.Prime 105310300298179943728621 := by
  apply lucas_primality 105310300298179943728621 (6 : ZMod 105310300298179943728621)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (31, 1), (71, 1), (88604759030558453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (31, 1), (71, 1), (88604759030558453, 1)] : List FactorBlock).map factorBlockValue).prod) = 105310300298179943728621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_31
      · exact prime_oneHundredThirtyTwoDZ_71
      · exact prime_oneHundredThirtyTwoDZ_88604759030558453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 105310300298179943728621) ^ 52655150149089971864310 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 105310300298179943728621) ^ 35103433432726647909540 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 105310300298179943728621) ^ 21062060059635988745724 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 105310300298179943728621) ^ 3397106461231611088020 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 105310300298179943728621) ^ 1483243666171548503220 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 105310300298179943728621) ^ 1188540 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_215121178501522590773563 : Nat.Prime 215121178501522590773563 := by
  apply lucas_primality 215121178501522590773563 (2 : ZMod 215121178501522590773563)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) = 215121178501522590773563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_35853529750253765128927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 215121178501522590773563) ^ 107560589250761295386781 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 71707059500507530257854 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 6 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_270729353794970093039171 : Nat.Prime 270729353794970093039171 := by
  apply lucas_primality 270729353794970093039171 (2 : ZMod 270729353794970093039171)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (11, 1), (36697, 1), (1368724432009199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (11, 1), (36697, 1), (1368724432009199, 1)] : List FactorBlock).map factorBlockValue).prod) = 270729353794970093039171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_36697
      · exact prime_oneHundredThirtyTwoDZ_1368724432009199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 270729353794970093039171) ^ 135364676897485046519585 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 270729353794970093039171) ^ 54145870758994018607834 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 270729353794970093039171) ^ 38675621970710013291310 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 270729353794970093039171) ^ 24611759435906372094470 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 270729353794970093039171) ^ 7377424688529582610 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 270729353794970093039171) ^ 197796830 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_324948733184189665620353 : Nat.Prime 324948733184189665620353 := by
  apply lucas_primality 324948733184189665620353 (3 : ZMod 324948733184189665620353)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (12995087869, 1), (195355506911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (12995087869, 1), (195355506911, 1)] : List FactorBlock).map factorBlockValue).prod) = 324948733184189665620353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_12995087869
      · exact prime_oneHundredThirtyTwoDZ_195355506911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 324948733184189665620353) ^ 162474366592094832810176 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 324948733184189665620353) ^ 25005504884608 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 324948733184189665620353) ^ 1663371247232 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_440903816895385998795037 : Nat.Prime 440903816895385998795037 := by
  apply lucas_primality 440903816895385998795037 (2 : ZMod 440903816895385998795037)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (191, 1), (19630027, 1), (890872725739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (191, 1), (19630027, 1), (890872725739, 1)] : List FactorBlock).map factorBlockValue).prod) = 440903816895385998795037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_191
      · exact prime_oneHundredThirtyTwoDZ_19630027
      · exact prime_oneHundredThirtyTwoDZ_890872725739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 440903816895385998795037) ^ 220451908447692999397518 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 440903816895385998795037) ^ 146967938965128666265012 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 440903816895385998795037) ^ 40082165172307818072276 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 440903816895385998795037) ^ 2308396947096261773796 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 440903816895385998795037) ^ 22460683161331668 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 440903816895385998795037) ^ 494912240724 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_649897466368379331240707 : Nat.Prime 649897466368379331240707 := by
  apply lucas_primality 649897466368379331240707 (2 : ZMod 649897466368379331240707)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (324948733184189665620353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (324948733184189665620353, 1)] : List FactorBlock).map factorBlockValue).prod) = 649897466368379331240707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_324948733184189665620353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 649897466368379331240707) ^ 324948733184189665620353 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 649897466368379331240707) ^ 2 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_878899926231809511221431 : Nat.Prime 878899926231809511221431 := by
  apply lucas_primality 878899926231809511221431 (6 : ZMod 878899926231809511221431)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) = 878899926231809511221431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_797
      · exact prime_oneHundredThirtyTwoDZ_125287
      · exact prime_oneHundredThirtyTwoDZ_13971226936099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 878899926231809511221431) ^ 439449963115904755610715 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 292966642077269837073810 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 175779985246361902244286 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 125557132318829930174490 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 1102760258760112310190 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 7015092756884668890 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 62907855570 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_983533507497054051322853 : Nat.Prime 983533507497054051322853 := by
  apply lucas_primality 983533507497054051322853 (2 : ZMod 983533507497054051322853)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (643, 1), (2843, 1), (149173, 1), (20969238383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (643, 1), (2843, 1), (149173, 1), (20969238383, 1)] : List FactorBlock).map factorBlockValue).prod) = 983533507497054051322853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_43
      · exact prime_oneHundredThirtyTwoDZ_643
      · exact prime_oneHundredThirtyTwoDZ_2843
      · exact prime_oneHundredThirtyTwoDZ_149173
      · exact prime_oneHundredThirtyTwoDZ_20969238383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 983533507497054051322853) ^ 491766753748527025661426 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 983533507497054051322853) ^ 22872872267373350030764 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 983533507497054051322853) ^ 1529601100306460421964 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 983533507497054051322853) ^ 345949176045393616364 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 983533507497054051322853) ^ 6593240784170419924 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 983533507497054051322853) ^ 46903635198044 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1092094617188171788686413 : Nat.Prime 1092094617188171788686413 := by
  apply lucas_primality 1092094617188171788686413 (2 : ZMod 1092094617188171788686413)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (997, 1), (273845189866642875799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (997, 1), (273845189866642875799, 1)] : List FactorBlock).map factorBlockValue).prod) = 1092094617188171788686413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_997
      · exact prime_oneHundredThirtyTwoDZ_273845189866642875799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1092094617188171788686413) ^ 546047308594085894343206 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1092094617188171788686413) ^ 1095380759466571503196 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1092094617188171788686413) ^ 3988 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1374039010552951393605217 : Nat.Prime 1374039010552951393605217 := by
  apply lucas_primality 1374039010552951393605217 (5 : ZMod 1374039010552951393605217)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (164535439, 1), (28996602893813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (164535439, 1), (28996602893813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1374039010552951393605217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_164535439
      · exact prime_oneHundredThirtyTwoDZ_28996602893813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1374039010552951393605217) ^ 687019505276475696802608 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1374039010552951393605217) ^ 458013003517650464535072 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1374039010552951393605217) ^ 8351021633418144 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1374039010552951393605217) ^ 47386206432 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_3567068084607372809862851 : Nat.Prime 3567068084607372809862851 := by
  apply lucas_primality 3567068084607372809862851 (2 : ZMod 3567068084607372809862851)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (179, 1), (1931, 1), (11801, 1), (830329, 1), (21063817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (179, 1), (1931, 1), (11801, 1), (830329, 1), (21063817, 1)] : List FactorBlock).map factorBlockValue).prod) = 3567068084607372809862851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_179
      · exact prime_oneHundredThirtyTwoDZ_1931
      · exact prime_oneHundredThirtyTwoDZ_11801
      · exact prime_oneHundredThirtyTwoDZ_830329
      · exact prime_oneHundredThirtyTwoDZ_21063817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3567068084607372809862851) ^ 1783534042303686404931425 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3567068084607372809862851) ^ 713413616921474561972570 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3567068084607372809862851) ^ 19927754662611021284150 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3567068084607372809862851) ^ 1847264673540845577350 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3567068084607372809862851) ^ 302268289518462232850 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3567068084607372809862851) ^ 4295969530881581650 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3567068084607372809862851) ^ 169345759346816050 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_4472636383743338313409943 : Nat.Prime 4472636383743338313409943 := by
  apply lucas_primality 4472636383743338313409943 (5 : ZMod 4472636383743338313409943)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (70496453, 1), (4531774490983801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (70496453, 1), (4531774490983801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4472636383743338313409943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_70496453
      · exact prime_oneHundredThirtyTwoDZ_4531774490983801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4472636383743338313409943) ^ 2236318191871669156704971 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 4472636383743338313409943) ^ 638948054820476901915706 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 4472636383743338313409943) ^ 63444842873773214 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 4472636383743338313409943) ^ 986950342 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_15414779603079075506864849 : Nat.Prime 15414779603079075506864849 := by
  apply lucas_primality 15414779603079075506864849 (3 : ZMod 15414779603079075506864849)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (61, 1), (179, 1), (2051946415555650209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (61, 1), (179, 1), (2051946415555650209, 1)] : List FactorBlock).map factorBlockValue).prod) = 15414779603079075506864849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_43
      · exact prime_oneHundredThirtyTwoDZ_61
      · exact prime_oneHundredThirtyTwoDZ_179
      · exact prime_oneHundredThirtyTwoDZ_2051946415555650209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15414779603079075506864849) ^ 7707389801539537753432424 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15414779603079075506864849) ^ 358483246583234314113136 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15414779603079075506864849) ^ 252701304968509434538768 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15414779603079075506864849) ^ 86116087168039527971312 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15414779603079075506864849) ^ 7512272 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1130863976098351887184780661 : Nat.Prime 1130863976098351887184780661 := by
  apply lucas_primality 1130863976098351887184780661 (2 : ZMod 1130863976098351887184780661)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (56645794981, 1), (998188812141893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (56645794981, 1), (998188812141893, 1)] : List FactorBlock).map factorBlockValue).prod) = 1130863976098351887184780661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_56645794981
      · exact prime_oneHundredThirtyTwoDZ_998188812141893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1130863976098351887184780661) ^ 565431988049175943592390330 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130863976098351887184780661) ^ 226172795219670377436956132 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130863976098351887184780661) ^ 19963776242837860 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130863976098351887184780661) ^ 1132915899620 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_1625616965641380837828122201 : Nat.Prime 1625616965641380837828122201 := by
  apply lucas_primality 1625616965641380837828122201 (3 : ZMod 1625616965641380837828122201)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1625616965641380837828122201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_171401
      · exact prime_oneHundredThirtyTwoDZ_714027719
      · exact prime_oneHundredThirtyTwoDZ_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1625616965641380837828122201) ^ 812808482820690418914061100 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 325123393128276167565624440 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 147783360512852803438920200 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 9484291023047595042200 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 2276686075882413800 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 269247143141501800 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_2558348011501189515270487397 : Nat.Prime 2558348011501189515270487397 := by
  apply lucas_primality 2558348011501189515270487397 (2 : ZMod 2558348011501189515270487397)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (4472636383743338313409943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (4472636383743338313409943, 1)] : List FactorBlock).map factorBlockValue).prod) = 2558348011501189515270487397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_4472636383743338313409943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2558348011501189515270487397) ^ 1279174005750594757635243698 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2558348011501189515270487397) ^ 232577091954653592297317036 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2558348011501189515270487397) ^ 196796000884706885790037492 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2558348011501189515270487397) ^ 572 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_4589977314752134130338227391 : Nat.Prime 4589977314752134130338227391 := by
  apply lucas_primality 4589977314752134130338227391 (6 : ZMod 4589977314752134130338227391)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (7591, 1), (1550411355806685423811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (7591, 1), (1550411355806685423811, 1)] : List FactorBlock).map factorBlockValue).prod) = 4589977314752134130338227391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_7591
      · exact prime_oneHundredThirtyTwoDZ_1550411355806685423811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4589977314752134130338227391) ^ 2294988657376067065169113695 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4589977314752134130338227391) ^ 1529992438250711376779409130 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4589977314752134130338227391) ^ 917995462950426826067645478 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4589977314752134130338227391) ^ 353075178057856471564479030 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4589977314752134130338227391) ^ 604660428764607315286290 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4589977314752134130338227391) ^ 2960490 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_6002278026983560016596143509 : Nat.Prime 6002278026983560016596143509 := by
  apply lucas_primality 6002278026983560016596143509 (2 : ZMod 6002278026983560016596143509)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (281, 1), (367, 1), (433, 1), (829, 1), (5790862669909049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (281, 1), (367, 1), (433, 1), (829, 1), (5790862669909049, 1)] : List FactorBlock).map factorBlockValue).prod) = 6002278026983560016596143509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_281
      · exact prime_oneHundredThirtyTwoDZ_367
      · exact prime_oneHundredThirtyTwoDZ_433
      · exact prime_oneHundredThirtyTwoDZ_829
      · exact prime_oneHundredThirtyTwoDZ_5790862669909049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6002278026983560016596143509) ^ 3001139013491780008298071754 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6002278026983560016596143509) ^ 857468289569080002370877644 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6002278026983560016596143509) ^ 21360420024852526749452468 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6002278026983560016596143509) ^ 16354980999955204404894124 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6002278026983560016596143509) ^ 13862073965320000038328276 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6002278026983560016596143509) ^ 7240383627241930056207652 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6002278026983560016596143509) ^ 1036508439092 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_6502467862565523351312488803 : Nat.Prime 6502467862565523351312488803 := by
  apply lucas_primality 6502467862565523351312488803 (2 : ZMod 6502467862565523351312488803)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 6502467862565523351312488803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_107
      · exact prime_oneHundredThirtyTwoDZ_43001837
      · exact prime_oneHundredThirtyTwoDZ_78511797954027271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6502467862565523351312488803) ^ 3251233931282761675656244401 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 2167489287521841117104162934 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 60770727687528255619742886 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 151213722859456523946 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 82821538062 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_12004556053967120033192287019 : Nat.Prime 12004556053967120033192287019 := by
  apply lucas_primality 12004556053967120033192287019 (2 : ZMod 12004556053967120033192287019)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6002278026983560016596143509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6002278026983560016596143509, 1)] : List FactorBlock).map factorBlockValue).prod) = 12004556053967120033192287019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_6002278026983560016596143509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 12004556053967120033192287019) ^ 6002278026983560016596143509 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12004556053967120033192287019) ^ 2 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_22294175528796080061642818753 : Nat.Prime 22294175528796080061642818753 := by
  apply lucas_primality 22294175528796080061642818753 (3 : ZMod 22294175528796080061642818753)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (23, 1), (59, 1), (1160644117, 1), (221173209466147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (23, 1), (59, 1), (1160644117, 1), (221173209466147, 1)] : List FactorBlock).map factorBlockValue).prod) = 22294175528796080061642818753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_23
      · exact prime_oneHundredThirtyTwoDZ_59
      · exact prime_oneHundredThirtyTwoDZ_1160644117
      · exact prime_oneHundredThirtyTwoDZ_221173209466147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22294175528796080061642818753) ^ 11147087764398040030821409376 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 22294175528796080061642818753) ^ 969311979512873046158383424 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 22294175528796080061642818753) ^ 377867381844001356976996928 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 22294175528796080061642818753) ^ 19208450895715934656 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 22294175528796080061642818753) ^ 100799620273216 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_39014807175393140107874932801 : Nat.Prime 39014807175393140107874932801 := by
  apply lucas_primality 39014807175393140107874932801 (7 : ZMod 39014807175393140107874932801)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393140107874932801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_171401
      · exact prime_oneHundredThirtyTwoDZ_714027719
      · exact prime_oneHundredThirtyTwoDZ_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 39014807175393140107874932801) ^ 19507403587696570053937466400 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 13004935725131046702624977600 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 7802961435078628021574986560 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 3546800652308467282534084800 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 227622984553142281012800 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 54640465821177931200 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 6461931435396043200 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_78029614350786280215749865623 : Nat.Prime 78029614350786280215749865623 := by
  apply lucas_primality 78029614350786280215749865623 (10 : ZMod 78029614350786280215749865623)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786280215749865623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_37
      · exact prime_oneHundredThirtyTwoDZ_31177
      · exact prime_oneHundredThirtyTwoDZ_3074685732733041494149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 78029614350786280215749865623) ^ 39014807175393140107874932811 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 78029614350786280215749865623) ^ 7093601304616934565068169602 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 78029614350786280215749865623) ^ 2108908495967196762587834206 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 78029614350786280215749865623) ^ 2502794186444695776237286 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (10 : ZMod 78029614350786280215749865623) ^ 25378078 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_78029614350786280215749865631 : Nat.Prime 78029614350786280215749865631 := by
  apply lucas_primality 78029614350786280215749865631 (19 : ZMod 78029614350786280215749865631)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (17, 1), (7591, 1), (1550411355806685423811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (17, 1), (7591, 1), (1550411355806685423811, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786280215749865631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_13
      · exact prime_oneHundredThirtyTwoDZ_17
      · exact prime_oneHundredThirtyTwoDZ_7591
      · exact prime_oneHundredThirtyTwoDZ_1550411355806685423811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 78029614350786280215749865631) ^ 39014807175393140107874932815 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 78029614350786280215749865631) ^ 26009871450262093405249955210 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 78029614350786280215749865631) ^ 15605922870157256043149973126 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 78029614350786280215749865631) ^ 6002278026983560016596143510 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 78029614350786280215749865631) ^ 4589977314752134130338227390 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 78029614350786280215749865631) ^ 10279227288998324359866930 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (19 : ZMod 78029614350786280215749865631) ^ 50328330 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_78029614350786280215749865641 : Nat.Prime 78029614350786280215749865641 := by
  apply lucas_primality 78029614350786280215749865641 (11 : ZMod 78029614350786280215749865641)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1873, 1), (3911, 1), (180272117, 1), (1477220469691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1873, 1), (3911, 1), (180272117, 1), (1477220469691, 1)] : List FactorBlock).map factorBlockValue).prod) = 78029614350786280215749865641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_5
      · exact prime_oneHundredThirtyTwoDZ_1873
      · exact prime_oneHundredThirtyTwoDZ_3911
      · exact prime_oneHundredThirtyTwoDZ_180272117
      · exact prime_oneHundredThirtyTwoDZ_1477220469691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 78029614350786280215749865641) ^ 39014807175393140107874932820 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 78029614350786280215749865641) ^ 15605922870157256043149973128 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 78029614350786280215749865641) ^ 41660231901113870910704680 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 78029614350786280215749865641) ^ 19951320468112063466057240 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 78029614350786280215749865641) ^ 432843501531555654920 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (11 : ZMod 78029614350786280215749865641) ^ 52821915179058040 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_156059228701572560431499731213 : Nat.Prime 156059228701572560431499731213 := by
  apply lucas_primality 156059228701572560431499731213 (2 : ZMod 156059228701572560431499731213)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (18541, 1), (21617, 1), (8348687, 1), (1295508299753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (18541, 1), (21617, 1), (8348687, 1), (1295508299753, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_18541
      · exact prime_oneHundredThirtyTwoDZ_21617
      · exact prime_oneHundredThirtyTwoDZ_8348687
      · exact prime_oneHundredThirtyTwoDZ_1295508299753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 156059228701572560431499731213) ^ 78029614350786280215749865606 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 156059228701572560431499731213) ^ 52019742900524186810499910404 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 156059228701572560431499731213) ^ 8416980135999814488511932 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 156059228701572560431499731213) ^ 7219282449071219893209036 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 156059228701572560431499731213) ^ 18692667326200222913076 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (2 : ZMod 156059228701572560431499731213) ^ 120461774526127404 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_156059228701572560431499731223 : Nat.Prime 156059228701572560431499731223 := by
  apply lucas_primality 156059228701572560431499731223 (5 : ZMod 156059228701572560431499731223)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_1153
      · exact prime_oneHundredThirtyTwoDZ_878899926231809511221431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 156059228701572560431499731223) ^ 78029614350786280215749865611 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 156059228701572560431499731223) ^ 22294175528796080061642818746 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 156059228701572560431499731223) ^ 14187202609233869130136339202 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 156059228701572560431499731223) ^ 135350588639698664728100374 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (5 : ZMod 156059228701572560431499731223) ^ 177562 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_156059228701572560431499731237 : Nat.Prime 156059228701572560431499731237 := by
  apply lucas_primality 156059228701572560431499731237 (23 : ZMod 156059228701572560431499731237)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 3), (5429792839, 1), (6982819718723939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 3), (5429792839, 1), (6982819718723939, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_3
      · exact prime_oneHundredThirtyTwoDZ_7
      · exact prime_oneHundredThirtyTwoDZ_5429792839
      · exact prime_oneHundredThirtyTwoDZ_6982819718723939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 156059228701572560431499731237) ^ 78029614350786280215749865618 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 156059228701572560431499731237) ^ 52019742900524186810499910412 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 156059228701572560431499731237) ^ 22294175528796080061642818748 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 156059228701572560431499731237) ^ 28741285962267732924 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (23 : ZMod 156059228701572560431499731237) ^ 22349027325324 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyTwoDZ_156059228701572560431499731289 : Nat.Prime 156059228701572560431499731289 := by
  apply lucas_primality 156059228701572560431499731289 (3 : ZMod 156059228701572560431499731289)
  · rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyTwoDZ_2
      · exact prime_oneHundredThirtyTwoDZ_11
      · exact prime_oneHundredThirtyTwoDZ_29
      · exact prime_oneHundredThirtyTwoDZ_113
      · exact prime_oneHundredThirtyTwoDZ_449
      · exact prime_oneHundredThirtyTwoDZ_1205269042013298899237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 156059228701572560431499731289) ^ 78029614350786280215749865644 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 156059228701572560431499731289) ^ 14187202609233869130136339208 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 156059228701572560431499731289) ^ 5381352713847329670051714872 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 156059228701572560431499731289) ^ 1381055121252854517092917976 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 156059228701572560431499731289) ^ 347570665259627083366369112 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide
    · change (3 : ZMod 156059228701572560431499731289) ^ 129480824 ≠ 1
      rw [← oneHundredThirtyTwoDZFastPow_eq_pow]
      decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731200 : Nat.totient 156059228701572560431499731200 = 37832319506721499351326720000 := by
  rw [← show ((([(2, 8), (3, 1), (5, 2), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_11, prime_oneHundredThirtyTwoDZ_171401, prime_oneHundredThirtyTwoDZ_714027719, prime_oneHundredThirtyTwoDZ_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731201 : Nat.totient 156059228701572560431499731201 = 128903904656002075240119716160 := by
  rw [← show ((([(7, 1), (29, 1), (719, 1), (1871, 1), (571466452238032796483, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_29, prime_oneHundredThirtyTwoDZ_719, prime_oneHundredThirtyTwoDZ_1871, prime_oneHundredThirtyTwoDZ_571466452238032796483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731202 : Nat.totient 156059228701572560431499731202 = 78029160945388160081784599808 := by
  rw [← show ((([(2, 1), (172097, 1), (149153487139, 1), (3039854166347, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_172097, prime_oneHundredThirtyTwoDZ_149153487139, prime_oneHundredThirtyTwoDZ_3039854166347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731203 : Nat.totient 156059228701572560431499731203 = 104035586416250163345012216480 := by
  rw [← show ((([(3, 2), (26681, 1), (649897466368379331240707, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_26681, prime_oneHundredThirtyTwoDZ_649897466368379331240707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731204 : Nat.totient 156059228701572560431499731204 = 78029614350786280215749865600 := by
  rw [← show ((([(2, 2), (39014807175393140107874932801, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_39014807175393140107874932801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731205 : Nat.totient 156059228701572560431499731205 = 121176692368752267824057395200 := by
  rw [← show ((([(5, 1), (59, 1), (79, 1), (113021, 1), (59249024358708502561, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_59, prime_oneHundredThirtyTwoDZ_79, prime_oneHundredThirtyTwoDZ_113021, prime_oneHundredThirtyTwoDZ_59249024358708502561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731206 : Nat.totient 156059228701572560431499731206 = 52019736491952858067124884704 := by
  rw [← show ((([(2, 1), (3, 1), (8146423, 1), (2267521189, 1), (1408055893883, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_8146423, prime_oneHundredThirtyTwoDZ_2267521189, prime_oneHundredThirtyTwoDZ_1408055893883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731207 : Nat.totient 156059228701572560431499731207 = 151825119037921336083985907712 := by
  rw [← show ((([(37, 1), (9323, 1), (25657969, 1), (17632332697524353, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_37, prime_oneHundredThirtyTwoDZ_9323, prime_oneHundredThirtyTwoDZ_25657969, prime_oneHundredThirtyTwoDZ_17632332697524353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731208 : Nat.totient 156059228701572560431499731208 = 61134864486695030790043729920 := by
  rw [← show ((([(2, 3), (7, 1), (13, 1), (281, 1), (367, 1), (433, 1), (829, 1), (5790862669909049, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_13, prime_oneHundredThirtyTwoDZ_281, prime_oneHundredThirtyTwoDZ_367, prime_oneHundredThirtyTwoDZ_433, prime_oneHundredThirtyTwoDZ_829, prime_oneHundredThirtyTwoDZ_5790862669909049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731209 : Nat.totient 156059228701572560431499731209 = 97172038826304722555760875520 := by
  rw [← show ((([(3, 1), (17, 2), (131, 1), (1374039010552951393605217, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_17, prime_oneHundredThirtyTwoDZ_131, prime_oneHundredThirtyTwoDZ_1374039010552951393605217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731210 : Nat.totient 156059228701572560431499731210 = 62267108928029628466713350400 := by
  rw [← show ((([(2, 1), (5, 1), (401, 1), (68239, 1), (570311894838924320639, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_401, prime_oneHundredThirtyTwoDZ_68239, prime_oneHundredThirtyTwoDZ_570311894838924320639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731211 : Nat.totient 156059228701572560431499731211 = 129810842358788432184390381600 := by
  rw [← show ((([(11, 1), (19, 1), (31, 1), (503, 1), (47886543588161587791203, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_11, prime_oneHundredThirtyTwoDZ_19, prime_oneHundredThirtyTwoDZ_31, prime_oneHundredThirtyTwoDZ_503, prime_oneHundredThirtyTwoDZ_47886543588161587791203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731212 : Nat.totient 156059228701572560431499731212 = 52014524712480375496695336960 := by
  rw [← show ((([(2, 2), (3, 2), (18541, 1), (21617, 1), (8348687, 1), (1295508299753, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_18541, prime_oneHundredThirtyTwoDZ_21617, prime_oneHundredThirtyTwoDZ_8348687, prime_oneHundredThirtyTwoDZ_1295508299753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731213 : Nat.totient 156059228701572560431499731213 = 156059228701572560431499731212 := by
  rw [← show ((([(156059228701572560431499731213, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_156059228701572560431499731213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731214 : Nat.totient 156059228701572560431499731214 = 74447539848070193481207148800 := by
  rw [← show ((([(2, 1), (43, 1), (53, 1), (227, 1), (1027139401, 1), (146845245298579, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_43, prime_oneHundredThirtyTwoDZ_53, prime_oneHundredThirtyTwoDZ_227, prime_oneHundredThirtyTwoDZ_1027139401, prime_oneHundredThirtyTwoDZ_146845245298579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731215 : Nat.totient 156059228701572560431499731215 = 71341307764832520983981960064 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (1322917, 1), (1123485727816941907499, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_1322917, prime_oneHundredThirtyTwoDZ_1123485727816941907499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731216 : Nat.totient 156059228701572560431499731216 = 76007469459372337086230002560 := by
  rw [← show ((([(2, 4), (47, 1), (211, 1), (983533507497054051322853, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_47, prime_oneHundredThirtyTwoDZ_211, prime_oneHundredThirtyTwoDZ_983533507497054051322853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731217 : Nat.totient 156059228701572560431499731217 = 153500880690071370916229243760 := by
  rw [← show ((([(61, 1), (2558348011501189515270487397, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_61, prime_oneHundredThirtyTwoDZ_2558348011501189515270487397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731218 : Nat.totient 156059228701572560431499731218 = 49758014948327483036130349040 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (1130863976098351887184780661, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_23, prime_oneHundredThirtyTwoDZ_1130863976098351887184780661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731219 : Nat.totient 156059228701572560431499731219 = 156037065171020443642128019200 := by
  rw [← show ((([(7393, 1), (148403, 1), (51515071, 1), (2761161230591, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_7393, prime_oneHundredThirtyTwoDZ_148403, prime_oneHundredThirtyTwoDZ_51515071, prime_oneHundredThirtyTwoDZ_2761161230591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731220 : Nat.totient 156059228701572560431499731220 = 60900048236466831302898278400 := by
  rw [← show ((([(2, 2), (5, 1), (41, 1), (67181, 1), (293269, 1), (9659685377123689, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_41, prime_oneHundredThirtyTwoDZ_67181, prime_oneHundredThirtyTwoDZ_293269, prime_oneHundredThirtyTwoDZ_9659685377123689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731221 : Nat.totient 156059228701572560431499731221 = 94270355924135671679427100800 := by
  rw [← show ((([(3, 4), (13, 2), (71, 1), (229, 1), (701170928896133910271, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_13, prime_oneHundredThirtyTwoDZ_71, prime_oneHundredThirtyTwoDZ_229, prime_oneHundredThirtyTwoDZ_701170928896133910271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731222 : Nat.totient 156059228701572560431499731222 = 60749562901142673415625241600 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_11, prime_oneHundredThirtyTwoDZ_1153, prime_oneHundredThirtyTwoDZ_878899926231809511221431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731223 : Nat.totient 156059228701572560431499731223 = 156059228701572560431499731222 := by
  rw [← show ((([(156059228701572560431499731223, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_156059228701572560431499731223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731224 : Nat.totient 156059228701572560431499731224 = 51422566509003960098512260480 := by
  rw [← show ((([(2, 3), (3, 1), (167, 1), (181, 1), (215121178501522590773563, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_167, prime_oneHundredThirtyTwoDZ_181, prime_oneHundredThirtyTwoDZ_215121178501522590773563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731225 : Nat.totient 156059228701572560431499731225 = 124847382961229145072999353280 := by
  rw [← show ((([(5, 2), (4332477976933, 1), (1440831132044653, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_4332477976933, prime_oneHundredThirtyTwoDZ_1440831132044653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731226 : Nat.totient 156059228701572560431499731226 = 73316757077409095941730457600 := by
  rw [← show ((([(2, 1), (17, 1), (601, 1), (113093, 1), (2040559, 1), (33094146576847, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_17, prime_oneHundredThirtyTwoDZ_601, prime_oneHundredThirtyTwoDZ_113093, prime_oneHundredThirtyTwoDZ_2040559, prime_oneHundredThirtyTwoDZ_33094146576847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731227 : Nat.totient 156059228701572560431499731227 = 104039485800504078609746497032 := by
  rw [← show ((([(3, 1), (191145530867, 1), (272147314481131027, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_191145530867, prime_oneHundredThirtyTwoDZ_272147314481131027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731228 : Nat.totient 156059228701572560431499731228 = 78029611218408215818687398912 := by
  rw [← show ((([(2, 2), (24910663, 1), (1566189032198506322689, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_24910663, prime_oneHundredThirtyTwoDZ_1566189032198506322689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731229 : Nat.totient 156059228701572560431499731229 = 132991836014626199368576856064 := by
  rw [← show ((([(7, 1), (173, 1), (15899909, 1), (342432449, 1), (23668773979, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_173, prime_oneHundredThirtyTwoDZ_15899909, prime_oneHundredThirtyTwoDZ_342432449, prime_oneHundredThirtyTwoDZ_23668773979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731230 : Nat.totient 156059228701572560431499731230 = 38059838537176498098346278912 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (19, 1), (29, 1), (12893, 1), (13873, 1), (83639, 1), (210359508407, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_19, prime_oneHundredThirtyTwoDZ_29, prime_oneHundredThirtyTwoDZ_12893, prime_oneHundredThirtyTwoDZ_13873, prime_oneHundredThirtyTwoDZ_83639, prime_oneHundredThirtyTwoDZ_210359508407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731231 : Nat.totient 156059228701572560431499731231 = 154125314571240035791274875680 := by
  rw [← show ((([(139, 1), (191, 1), (2291465917703, 1), (2565239310373, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_139, prime_oneHundredThirtyTwoDZ_191, prime_oneHundredThirtyTwoDZ_2291465917703, prime_oneHundredThirtyTwoDZ_2565239310373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731232 : Nat.totient 156059228701572560431499731232 = 77475411852425014235120167680 := by
  rw [← show ((([(2, 5), (197, 1), (491, 1), (50418713460813862866463, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_197, prime_oneHundredThirtyTwoDZ_491, prime_oneHundredThirtyTwoDZ_50418713460813862866463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731233 : Nat.totient 156059228701572560431499731233 = 94568841583050739932652060800 := by
  rw [← show ((([(3, 1), (11, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_11, prime_oneHundredThirtyTwoDZ_7561, prime_oneHundredThirtyTwoDZ_2416168199, prime_oneHundredThirtyTwoDZ_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731234 : Nat.totient 156059228701572560431499731234 = 72027336323802720199153722096 := by
  rw [← show ((([(2, 1), (13, 1), (6002278026983560016596143509, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_13, prime_oneHundredThirtyTwoDZ_6002278026983560016596143509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731235 : Nat.totient 156059228701572560431499731235 = 124809451930685662418293747200 := by
  rw [← show ((([(5, 1), (5471, 1), (8263, 1), (26344529, 1), (26207436719791, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_5471, prime_oneHundredThirtyTwoDZ_8263, prime_oneHundredThirtyTwoDZ_26344529, prime_oneHundredThirtyTwoDZ_26207436719791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731236 : Nat.totient 156059228701572560431499731236 = 44588351049380357748629907744 := by
  rw [← show ((([(2, 2), (3, 1), (7, 3), (5429792839, 1), (6982819718723939, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_5429792839, prime_oneHundredThirtyTwoDZ_6982819718723939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731237 : Nat.totient 156059228701572560431499731237 = 156059228701572560431499731236 := by
  rw [← show ((([(156059228701572560431499731237, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_156059228701572560431499731237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731238 : Nat.totient 156059228701572560431499731238 = 78027078444379568510647754400 := by
  rw [← show ((([(2, 1), (36709, 1), (190181, 1), (11176859198602392011, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_36709, prime_oneHundredThirtyTwoDZ_190181, prime_oneHundredThirtyTwoDZ_11176859198602392011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731239 : Nat.totient 156059228701572560431499731239 = 102188496569303385508743751680 := by
  rw [← show ((([(3, 2), (73, 1), (241, 1), (19024693, 1), (51807112427513579, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_73, prime_oneHundredThirtyTwoDZ_241, prime_oneHundredThirtyTwoDZ_19024693, prime_oneHundredThirtyTwoDZ_51807112427513579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731240 : Nat.totient 156059228701572560431499731240 = 62419359810968304651111035200 := by
  rw [← show ((([(2, 3), (5, 1), (14411, 1), (270729353794970093039171, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_14411, prime_oneHundredThirtyTwoDZ_270729353794970093039171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731241 : Nat.totient 156059228701572560431499731241 = 148846485283922528019531694080 := by
  rw [← show ((([(23, 1), (383, 1), (7759, 1), (13313, 1), (24821, 1), (103349, 1), (66858343, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_23, prime_oneHundredThirtyTwoDZ_383, prime_oneHundredThirtyTwoDZ_7759, prime_oneHundredThirtyTwoDZ_13313, prime_oneHundredThirtyTwoDZ_24821, prime_oneHundredThirtyTwoDZ_103349, prime_oneHundredThirtyTwoDZ_66858343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731242 : Nat.totient 156059228701572560431499731242 = 50341686662498313363063078960 := by
  rw [← show ((([(2, 1), (3, 1), (31, 1), (3262940519, 1), (257138647306974463, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_31, prime_oneHundredThirtyTwoDZ_3262940519, prime_oneHundredThirtyTwoDZ_257138647306974463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731243 : Nat.totient 156059228701572560431499731243 = 125896520633157099333953617536 := by
  rw [← show ((([(7, 1), (17, 1), (2860024003019, 1), (458535343949863, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_17, prime_oneHundredThirtyTwoDZ_2860024003019, prime_oneHundredThirtyTwoDZ_458535343949863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731244 : Nat.totient 156059228701572560431499731244 = 69016609730653417167521794560 := by
  rw [← show ((([(2, 2), (11, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_11, prime_oneHundredThirtyTwoDZ_37, prime_oneHundredThirtyTwoDZ_31177, prime_oneHundredThirtyTwoDZ_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731245 : Nat.totient 156059228701572560431499731245 = 83229084320369520116013956352 := by
  rw [← show ((([(3, 1), (5, 1), (33533, 1), (3742237, 1), (82907629848971723, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_33533, prime_oneHundredThirtyTwoDZ_3742237, prime_oneHundredThirtyTwoDZ_82907629848971723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731246 : Nat.totient 156059228701572560431499731246 = 78029614350786280215749865622 := by
  rw [← show ((([(2, 1), (78029614350786280215749865623, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_78029614350786280215749865623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731247 : Nat.totient 156059228701572560431499731247 = 144054672647605440398307444216 := by
  rw [← show ((([(13, 1), (12004556053967120033192287019, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_13, prime_oneHundredThirtyTwoDZ_12004556053967120033192287019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731248 : Nat.totient 156059228701572560431499731248 = 51533575880619876138889678080 := by
  rw [← show ((([(2, 4), (3, 3), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_107, prime_oneHundredThirtyTwoDZ_43001837, prime_oneHundredThirtyTwoDZ_78511797954027271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731249 : Nat.totient 156059228701572560431499731249 = 147845584298845752158321252496 := by
  rw [← show ((([(19, 1), (187894423, 1), (43714142680393659277, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_19, prime_oneHundredThirtyTwoDZ_187894423, prime_oneHundredThirtyTwoDZ_43714142680393659277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731250 : Nat.totient 156059228701572560431499731250 = 53506021269110592147942750000 := by
  rw [← show ((([(2, 1), (5, 5), (7, 1), (3567068084607372809862851, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_3567068084607372809862851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731251 : Nat.totient 156059228701572560431499731251 = 104038333762715918893161129888 := by
  rw [← show ((([(3, 1), (90359, 1), (163361827, 1), (3524083610216669, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_90359, prime_oneHundredThirtyTwoDZ_163361827, prime_oneHundredThirtyTwoDZ_3524083610216669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731252 : Nat.totient 156059228701572560431499731252 = 77923161943727238780312153600 := by
  rw [← show ((([(2, 2), (733, 1), (2786044081081, 1), (19104580532281, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_733, prime_oneHundredThirtyTwoDZ_2786044081081, prime_oneHundredThirtyTwoDZ_19104580532281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731253 : Nat.totient 156059228701572560431499731253 = 155846625168113742972470810848 := by
  rw [← show ((([(743, 1), (60779, 1), (3455787998550372376649, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_743, prime_oneHundredThirtyTwoDZ_60779, prime_oneHundredThirtyTwoDZ_3455787998550372376649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731254 : Nat.totient 156059228701572560431499731254 = 52006805884055245853046585600 := by
  rw [← show ((([(2, 1), (3, 1), (4021, 1), (700722673081, 1), (9231195796909, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_4021, prime_oneHundredThirtyTwoDZ_700722673081, prime_oneHundredThirtyTwoDZ_9231195796909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731255 : Nat.totient 156059228701572560431499731255 = 113497620341393439530277742080 := by
  rw [← show ((([(5, 1), (11, 1), (213150073, 1), (13311937837557174217, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_11, prime_oneHundredThirtyTwoDZ_213150073, prime_oneHundredThirtyTwoDZ_13311937837557174217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731256 : Nat.totient 156059228701572560431499731256 = 77899347881704414463060158080 := by
  rw [← show ((([(2, 3), (599, 1), (74166855821, 1), (439099334161333, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_599, prime_oneHundredThirtyTwoDZ_74166855821, prime_oneHundredThirtyTwoDZ_439099334161333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731257 : Nat.totient 156059228701572560431499731257 = 85745537176140353828508724224 := by
  rw [← show ((([(3, 2), (7, 1), (43, 1), (67, 1), (1499, 1), (14383849, 1), (39877589675069, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_43, prime_oneHundredThirtyTwoDZ_67, prime_oneHundredThirtyTwoDZ_1499, prime_oneHundredThirtyTwoDZ_14383849, prime_oneHundredThirtyTwoDZ_39877589675069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731258 : Nat.totient 156059228701572560431499731258 = 77896524439632190327030195200 := by
  rw [← show ((([(2, 1), (631, 1), (19163, 1), (19391, 1), (57839, 1), (5753678878657, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_631, prime_oneHundredThirtyTwoDZ_19163, prime_oneHundredThirtyTwoDZ_19391, prime_oneHundredThirtyTwoDZ_57839, prime_oneHundredThirtyTwoDZ_5753678878657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731259 : Nat.totient 156059228701572560431499731259 = 149836627148341166970575184000 := by
  rw [← show ((([(29, 1), (223, 1), (911, 1), (235043, 1), (556651, 1), (202459380199, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_29, prime_oneHundredThirtyTwoDZ_223, prime_oneHundredThirtyTwoDZ_911, prime_oneHundredThirtyTwoDZ_235043, prime_oneHundredThirtyTwoDZ_556651, prime_oneHundredThirtyTwoDZ_202459380199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731260 : Nat.totient 156059228701572560431499731260 = 36150135369439464550557388800 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (13, 1), (17, 1), (7591, 1), (1550411355806685423811, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_13, prime_oneHundredThirtyTwoDZ_17, prime_oneHundredThirtyTwoDZ_7591, prime_oneHundredThirtyTwoDZ_1550411355806685423811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731261 : Nat.totient 156059228701572560431499731261 = 148990217805288836712818565120 := by
  rw [← show ((([(41, 1), (89, 1), (97, 1), (440903816895385998795037, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_41, prime_oneHundredThirtyTwoDZ_89, prime_oneHundredThirtyTwoDZ_97, prime_oneHundredThirtyTwoDZ_440903816895385998795037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731262 : Nat.totient 156059228701572560431499731262 = 78029614350786280215749865630 := by
  rw [← show ((([(2, 1), (78029614350786280215749865631, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_78029614350786280215749865631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731263 : Nat.totient 156059228701572560431499731263 = 101825879720128116578868137216 := by
  rw [← show ((([(3, 1), (47, 1), (2181045234779, 1), (507464504994017, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_47, prime_oneHundredThirtyTwoDZ_2181045234779, prime_oneHundredThirtyTwoDZ_507464504994017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731264 : Nat.totient 156059228701572560431499731264 = 62890275497937405000900544512 := by
  rw [← show ((([(2, 6), (7, 1), (23, 1), (59, 1), (1160644117, 1), (221173209466147, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_23, prime_oneHundredThirtyTwoDZ_59, prime_oneHundredThirtyTwoDZ_1160644117, prime_oneHundredThirtyTwoDZ_221173209466147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731265 : Nat.totient 156059228701572560431499731265 = 124847020507478935343223592896 := by
  rw [← show ((([(5, 1), (376477, 1), (4049063, 1), (20475120607168103, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_376477, prime_oneHundredThirtyTwoDZ_4049063, prime_oneHundredThirtyTwoDZ_20475120607168103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731266 : Nat.totient 156059228701572560431499731266 = 47187418409712610807529664000 := by
  rw [← show ((([(2, 1), (3, 2), (11, 2), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_11, prime_oneHundredThirtyTwoDZ_461, prime_oneHundredThirtyTwoDZ_69997, prime_oneHundredThirtyTwoDZ_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731267 : Nat.totient 156059228701572560431499731267 = 152964749511788453888836206240 := by
  rw [← show ((([(53, 2), (1021, 1), (54414165710388903315703, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_53, prime_oneHundredThirtyTwoDZ_1021, prime_oneHundredThirtyTwoDZ_54414165710388903315703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731268 : Nat.totient 156059228701572560431499731268 = 73337595373891585235411158176 := by
  rw [← show ((([(2, 2), (19, 1), (127, 1), (23447, 1), (689580321364101784147, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_19, prime_oneHundredThirtyTwoDZ_127, prime_oneHundredThirtyTwoDZ_23447, prime_oneHundredThirtyTwoDZ_689580321364101784147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731269 : Nat.totient 156059228701572560431499731269 = 103340764260381921369561976320 := by
  rw [← show ((([(3, 1), (149, 1), (220021, 1), (382693673, 1), (4146355325719, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_149, prime_oneHundredThirtyTwoDZ_220021, prime_oneHundredThirtyTwoDZ_382693673, prime_oneHundredThirtyTwoDZ_4146355325719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731270 : Nat.totient 156059228701572560431499731270 = 61523933688704188073158154368 := by
  rw [← show ((([(2, 1), (5, 1), (83, 1), (419, 1), (128837, 1), (3483026166924771923, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_83, prime_oneHundredThirtyTwoDZ_419, prime_oneHundredThirtyTwoDZ_128837, prime_oneHundredThirtyTwoDZ_3483026166924771923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731271 : Nat.totient 156059228701572560431499731271 = 133765053172776480369856912512 := by
  rw [← show ((([(7, 1), (22294175528796080061642818753, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_22294175528796080061642818753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731272 : Nat.totient 156059228701572560431499731272 = 52019742900524186810499910416 := by
  rw [← show ((([(2, 3), (3, 1), (6502467862565523351312488803, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_6502467862565523351312488803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731273 : Nat.totient 156059228701572560431499731273 = 139141680894993901691334528000 := by
  rw [← show ((([(13, 1), (31, 1), (941, 1), (1181, 1), (84917759, 1), (4103423718869, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_13, prime_oneHundredThirtyTwoDZ_31, prime_oneHundredThirtyTwoDZ_941, prime_oneHundredThirtyTwoDZ_1181, prime_oneHundredThirtyTwoDZ_84917759, prime_oneHundredThirtyTwoDZ_4103423718869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731274 : Nat.totient 156059228701572560431499731274 = 78029606748138644771044853356 := by
  rw [← show ((([(2, 1), (10263479, 1), (7602647635444694748803, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_10263479, prime_oneHundredThirtyTwoDZ_7602647635444694748803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731275 : Nat.totient 156059228701572560431499731275 = 83231588232007181977952793600 := by
  rw [← show ((([(3, 3), (5, 2), (203584081, 1), (1135643102348768873, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_203584081, prime_oneHundredThirtyTwoDZ_1135643102348768873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731276 : Nat.totient 156059228701572560431499731276 = 77998784791580122064736130880 := by
  rw [← show ((([(2, 2), (2531, 1), (15414779603079075506864849, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_2531, prime_oneHundredThirtyTwoDZ_15414779603079075506864849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731277 : Nat.totient 156059228701572560431499731277 = 133526612554058939021467461120 := by
  rw [← show ((([(11, 1), (17, 1), (559319647, 1), (1492065108799822793, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_11, prime_oneHundredThirtyTwoDZ_17, prime_oneHundredThirtyTwoDZ_559319647, prime_oneHundredThirtyTwoDZ_1492065108799822793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731278 : Nat.totient 156059228701572560431499731278 = 43857275213112028684610872320 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (61, 1), (368873, 1), (117238469, 1), (1408520993987, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_61, prime_oneHundredThirtyTwoDZ_368873, prime_oneHundredThirtyTwoDZ_117238469, prime_oneHundredThirtyTwoDZ_1408520993987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731279 : Nat.totient 156059228701572560431499731279 = 156059123391272262251554520760 := by
  rw [← show ((([(1481899, 1), (105310300298179943728621, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_1481899, prime_oneHundredThirtyTwoDZ_105310300298179943728621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731280 : Nat.totient 156059228701572560431499731280 = 62374410414343149641409945600 := by
  rw [← show ((([(2, 4), (5, 1), (1873, 1), (3911, 1), (180272117, 1), (1477220469691, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_1873, prime_oneHundredThirtyTwoDZ_3911, prime_oneHundredThirtyTwoDZ_180272117, prime_oneHundredThirtyTwoDZ_1477220469691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731281 : Nat.totient 156059228701572560431499731281 = 101225124241867765921109885568 := by
  rw [← show ((([(3, 1), (37, 1), (40759, 1), (34493952189981709766969, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_37, prime_oneHundredThirtyTwoDZ_40759, prime_oneHundredThirtyTwoDZ_34493952189981709766969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731282 : Nat.totient 156059228701572560431499731282 = 78029614350786280215749865640 := by
  rw [← show ((([(2, 1), (78029614350786280215749865641, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_78029614350786280215749865641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731283 : Nat.totient 156059228701572560431499731283 = 156059228682103415698326067008 := by
  rw [← show ((([(8015720819, 1), (19469144725157943457, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_8015720819, prime_oneHundredThirtyTwoDZ_19469144725157943457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731284 : Nat.totient 156059228701572560431499731284 = 51361264104089020493821561152 := by
  rw [← show ((([(2, 2), (3, 2), (79, 1), (49471423, 1), (1109188763774599357, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_79, prime_oneHundredThirtyTwoDZ_49471423, prime_oneHundredThirtyTwoDZ_1109188763774599357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731285 : Nat.totient 156059228701572560431499731285 = 107012042537992121877997787424 := by
  rw [← show ((([(5, 1), (7, 2), (467334340387, 1), (1362999438800939, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_467334340387, prime_oneHundredThirtyTwoDZ_1362999438800939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731286 : Nat.totient 156059228701572560431499731286 = 72027316805558781144805037184 := by
  rw [← show ((([(2, 1), (13, 1), (3690257, 1), (1626520328254525366823, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_13, prime_oneHundredThirtyTwoDZ_3690257, prime_oneHundredThirtyTwoDZ_1626520328254525366823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731287 : Nat.totient 156059228701572560431499731287 = 93413405175807462117080936832 := by
  rw [← show ((([(3, 1), (19, 1), (23, 1), (109, 1), (1092094617188171788686413, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_19, prime_oneHundredThirtyTwoDZ_23, prime_oneHundredThirtyTwoDZ_109, prime_oneHundredThirtyTwoDZ_1092094617188171788686413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731288 : Nat.totient 156059228701572560431499731288 = 67732648986306399836233400320 := by
  rw [← show ((([(2, 3), (11, 1), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_11, prime_oneHundredThirtyTwoDZ_29, prime_oneHundredThirtyTwoDZ_113, prime_oneHundredThirtyTwoDZ_449, prime_oneHundredThirtyTwoDZ_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731289 : Nat.totient 156059228701572560431499731289 = 156059228701572560431499731288 := by
  rw [← show ((([(156059228701572560431499731289, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_156059228701572560431499731289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731290 : Nat.totient 156059228701572560431499731290 = 41508795928916145833633817600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (389, 1), (4186181, 1), (5930381, 1), (538664062567, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_389, prime_oneHundredThirtyTwoDZ_4186181, prime_oneHundredThirtyTwoDZ_5930381, prime_oneHundredThirtyTwoDZ_538664062567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731291 : Nat.totient 156059228701572560431499731291 = 154920109968057275006811528768 := by
  rw [← show ((([(137, 1), (561631199, 1), (2028232156090944157, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_137, prime_oneHundredThirtyTwoDZ_561631199, prime_oneHundredThirtyTwoDZ_2028232156090944157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731292 : Nat.totient 156059228701572560431499731292 = 65912064450642584962357348800 := by
  rw [← show ((([(2, 2), (7, 1), (71, 1), (2347, 1), (183571, 1), (182203163341714807, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_71, prime_oneHundredThirtyTwoDZ_2347, prime_oneHundredThirtyTwoDZ_183571, prime_oneHundredThirtyTwoDZ_182203163341714807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731293 : Nat.totient 156059228701572560431499731293 = 104039472173688077211517449096 := by
  rw [← show ((([(3, 2), (7634603, 1), (2271226716068239427359, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_7634603, prime_oneHundredThirtyTwoDZ_2271226716068239427359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731294 : Nat.totient 156059228701572560431499731294 = 73439637036034146085411638240 := by
  rw [← show ((([(2, 1), (17, 1), (4589977314752134130338227391, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_17, prime_oneHundredThirtyTwoDZ_4589977314752134130338227391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731295 : Nat.totient 156059228701572560431499731295 = 123508067339952628748603136000 := by
  rw [← show ((([(5, 1), (151, 1), (349, 1), (787, 1), (7278961, 1), (103388670991363, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_151, prime_oneHundredThirtyTwoDZ_349, prime_oneHundredThirtyTwoDZ_787, prime_oneHundredThirtyTwoDZ_7278961, prime_oneHundredThirtyTwoDZ_103388670991363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731296 : Nat.totient 156059228701572560431499731296 = 52019742900524186810499910400 := by
  rw [← show ((([(2, 5), (3, 1), (1625616965641380837828122201, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_1625616965641380837828122201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731297 : Nat.totient 156059228701572560431499731297 = 156059214412040999900243423328 := by
  rw [← show ((([(10928963, 1), (15696613913, 1), (909713258563, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_10928963, prime_oneHundredThirtyTwoDZ_15696613913, prime_oneHundredThirtyTwoDZ_909713258563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731298 : Nat.totient 156059228701572560431499731298 = 78029614317646182289648659264 := by
  rw [← show ((([(2, 1), (2354537833, 1), (33140097923746668553, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_2354537833, prime_oneHundredThirtyTwoDZ_33140097923746668553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731299 : Nat.totient 156059228701572560431499731299 = 73282438205198433349447680000 := by
  rw [← show ((([(3, 1), (7, 1), (11, 1), (13, 1), (101, 1), (103, 1), (1163, 1), (3221, 1), (20357, 1), (53279, 1), (1229519, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_3, prime_oneHundredThirtyTwoDZ_7, prime_oneHundredThirtyTwoDZ_11, prime_oneHundredThirtyTwoDZ_13, prime_oneHundredThirtyTwoDZ_101, prime_oneHundredThirtyTwoDZ_103, prime_oneHundredThirtyTwoDZ_1163, prime_oneHundredThirtyTwoDZ_3221, prime_oneHundredThirtyTwoDZ_20357, prime_oneHundredThirtyTwoDZ_53279, prime_oneHundredThirtyTwoDZ_1229519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731300 : Nat.totient 156059228701572560431499731300 = 60969256553550824710924492800 := by
  rw [← show ((([(2, 2), (5, 2), (43, 1), (23189, 1), (663991, 1), (2357093374911809, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_2, prime_oneHundredThirtyTwoDZ_5, prime_oneHundredThirtyTwoDZ_43, prime_oneHundredThirtyTwoDZ_23189, prime_oneHundredThirtyTwoDZ_663991, prime_oneHundredThirtyTwoDZ_2357093374911809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyTwoDZ_156059228701572560431499731301 : Nat.totient 156059228701572560431499731301 = 156040396786717742462930178048 := by
  rw [← show ((([(9829, 1), (52817, 1), (2179807673, 1), (137907604409, 1)] : List FactorBlock).map factorBlockValue).prod) = 156059228701572560431499731301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyTwoDZ_9829, prime_oneHundredThirtyTwoDZ_52817, prime_oneHundredThirtyTwoDZ_2179807673, prime_oneHundredThirtyTwoDZ_137907604409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThirtyTwoDZ : certifiedKill 1 156059228701572560431499731199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731200, phi_oneHundredThirtyTwoDZ_156059228701572560431499731201, phi_oneHundredThirtyTwoDZ_156059228701572560431499731202,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731203, phi_oneHundredThirtyTwoDZ_156059228701572560431499731204, phi_oneHundredThirtyTwoDZ_156059228701572560431499731205,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731206, phi_oneHundredThirtyTwoDZ_156059228701572560431499731207, phi_oneHundredThirtyTwoDZ_156059228701572560431499731208,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731209, phi_oneHundredThirtyTwoDZ_156059228701572560431499731210, phi_oneHundredThirtyTwoDZ_156059228701572560431499731211,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731212, phi_oneHundredThirtyTwoDZ_156059228701572560431499731213, phi_oneHundredThirtyTwoDZ_156059228701572560431499731214,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731215, phi_oneHundredThirtyTwoDZ_156059228701572560431499731216, phi_oneHundredThirtyTwoDZ_156059228701572560431499731217,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731218, phi_oneHundredThirtyTwoDZ_156059228701572560431499731219, phi_oneHundredThirtyTwoDZ_156059228701572560431499731220,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731221, phi_oneHundredThirtyTwoDZ_156059228701572560431499731222, phi_oneHundredThirtyTwoDZ_156059228701572560431499731223,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731224, phi_oneHundredThirtyTwoDZ_156059228701572560431499731225, phi_oneHundredThirtyTwoDZ_156059228701572560431499731226,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731227, phi_oneHundredThirtyTwoDZ_156059228701572560431499731228, phi_oneHundredThirtyTwoDZ_156059228701572560431499731229,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731230, phi_oneHundredThirtyTwoDZ_156059228701572560431499731231, phi_oneHundredThirtyTwoDZ_156059228701572560431499731232,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731233, phi_oneHundredThirtyTwoDZ_156059228701572560431499731234, phi_oneHundredThirtyTwoDZ_156059228701572560431499731235,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731236, phi_oneHundredThirtyTwoDZ_156059228701572560431499731237, phi_oneHundredThirtyTwoDZ_156059228701572560431499731238,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731239, phi_oneHundredThirtyTwoDZ_156059228701572560431499731240, phi_oneHundredThirtyTwoDZ_156059228701572560431499731241,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731242, phi_oneHundredThirtyTwoDZ_156059228701572560431499731243, phi_oneHundredThirtyTwoDZ_156059228701572560431499731244,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731245, phi_oneHundredThirtyTwoDZ_156059228701572560431499731246, phi_oneHundredThirtyTwoDZ_156059228701572560431499731247,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731248, phi_oneHundredThirtyTwoDZ_156059228701572560431499731249, phi_oneHundredThirtyTwoDZ_156059228701572560431499731250,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731251, phi_oneHundredThirtyTwoDZ_156059228701572560431499731252, phi_oneHundredThirtyTwoDZ_156059228701572560431499731253,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731254, phi_oneHundredThirtyTwoDZ_156059228701572560431499731255, phi_oneHundredThirtyTwoDZ_156059228701572560431499731256,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731257, phi_oneHundredThirtyTwoDZ_156059228701572560431499731258, phi_oneHundredThirtyTwoDZ_156059228701572560431499731259,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731260, phi_oneHundredThirtyTwoDZ_156059228701572560431499731261, phi_oneHundredThirtyTwoDZ_156059228701572560431499731262,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731263, phi_oneHundredThirtyTwoDZ_156059228701572560431499731264, phi_oneHundredThirtyTwoDZ_156059228701572560431499731265,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731266, phi_oneHundredThirtyTwoDZ_156059228701572560431499731267, phi_oneHundredThirtyTwoDZ_156059228701572560431499731268,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731269, phi_oneHundredThirtyTwoDZ_156059228701572560431499731270, phi_oneHundredThirtyTwoDZ_156059228701572560431499731271,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731272, phi_oneHundredThirtyTwoDZ_156059228701572560431499731273, phi_oneHundredThirtyTwoDZ_156059228701572560431499731274,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731275, phi_oneHundredThirtyTwoDZ_156059228701572560431499731276, phi_oneHundredThirtyTwoDZ_156059228701572560431499731277,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731278, phi_oneHundredThirtyTwoDZ_156059228701572560431499731279, phi_oneHundredThirtyTwoDZ_156059228701572560431499731280,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731281, phi_oneHundredThirtyTwoDZ_156059228701572560431499731282, phi_oneHundredThirtyTwoDZ_156059228701572560431499731283,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731284, phi_oneHundredThirtyTwoDZ_156059228701572560431499731285, phi_oneHundredThirtyTwoDZ_156059228701572560431499731286,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731287, phi_oneHundredThirtyTwoDZ_156059228701572560431499731288, phi_oneHundredThirtyTwoDZ_156059228701572560431499731289,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731290, phi_oneHundredThirtyTwoDZ_156059228701572560431499731291, phi_oneHundredThirtyTwoDZ_156059228701572560431499731292,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731293, phi_oneHundredThirtyTwoDZ_156059228701572560431499731294, phi_oneHundredThirtyTwoDZ_156059228701572560431499731295,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731296, phi_oneHundredThirtyTwoDZ_156059228701572560431499731297, phi_oneHundredThirtyTwoDZ_156059228701572560431499731298,
    phi_oneHundredThirtyTwoDZ_156059228701572560431499731299, phi_oneHundredThirtyTwoDZ_156059228701572560431499731300, phi_oneHundredThirtyTwoDZ_156059228701572560431499731301
    ]

end TotientTailPeriodKiller
end Erdos249257
