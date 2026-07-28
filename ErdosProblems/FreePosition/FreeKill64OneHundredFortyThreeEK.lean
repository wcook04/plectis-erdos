import Erdos249257.DiagonalPincerCertificatesT64
/- Kernel-checked off-diagonal certificate at a freely chosen position. -/
namespace Erdos249257
namespace TotientTailPeriodKiller
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private def oneHundredFortyThreeEKFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFortyThreeEKFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFortyThreeEKFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFortyThreeEKFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFortyThreeEKFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFortyThreeEKFastPow a n * oneHundredFortyThreeEKFastPow a n * a else oneHundredFortyThreeEKFastPow a n * oneHundredFortyThreeEKFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFortyThreeEK_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFortyThreeEK_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFortyThreeEK_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFortyThreeEK_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFortyThreeEK_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFortyThreeEK_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFortyThreeEK_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFortyThreeEK_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFortyThreeEK_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFortyThreeEK_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFortyThreeEK_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFortyThreeEK_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFortyThreeEK_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFortyThreeEK_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFortyThreeEK_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFortyThreeEK_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFortyThreeEK_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFortyThreeEK_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFortyThreeEK_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFortyThreeEK_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFortyThreeEK_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFortyThreeEK_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFortyThreeEK_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFortyThreeEK_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFortyThreeEK_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFortyThreeEK_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFortyThreeEK_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFortyThreeEK_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFortyThreeEK_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFortyThreeEK_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFortyThreeEK_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFortyThreeEK_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFortyThreeEK_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFortyThreeEK_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFortyThreeEK_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFortyThreeEK_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFortyThreeEK_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFortyThreeEK_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFortyThreeEK_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFortyThreeEK_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFortyThreeEK_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFortyThreeEK_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFortyThreeEK_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFortyThreeEK_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredFortyThreeEK_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFortyThreeEK_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFortyThreeEK_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFortyThreeEK_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFortyThreeEK_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredFortyThreeEK_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFortyThreeEK_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFortyThreeEK_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFortyThreeEK_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFortyThreeEK_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFortyThreeEK_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFortyThreeEK_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFortyThreeEK_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFortyThreeEK_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredFortyThreeEK_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFortyThreeEK_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFortyThreeEK_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFortyThreeEK_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFortyThreeEK_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredFortyThreeEK_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFortyThreeEK_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredFortyThreeEK_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredFortyThreeEK_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFortyThreeEK_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredFortyThreeEK_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredFortyThreeEK_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredFortyThreeEK_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredFortyThreeEK_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredFortyThreeEK_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFortyThreeEK_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredFortyThreeEK_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredFortyThreeEK_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredFortyThreeEK_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredFortyThreeEK_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredFortyThreeEK_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredFortyThreeEK_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFortyThreeEK_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredFortyThreeEK_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredFortyThreeEK_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredFortyThreeEK_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredFortyThreeEK_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredFortyThreeEK_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredFortyThreeEK_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredFortyThreeEK_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredFortyThreeEK_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredFortyThreeEK_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredFortyThreeEK_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredFortyThreeEK_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredFortyThreeEK_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredFortyThreeEK_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredFortyThreeEK_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredFortyThreeEK_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredFortyThreeEK_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredFortyThreeEK_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredFortyThreeEK_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredFortyThreeEK_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredFortyThreeEK_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredFortyThreeEK_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1999 : Nat.Prime 1999 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2459 : Nat.Prime 2459 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2539 : Nat.Prime 2539 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2659 : Nat.Prime 2659 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2687 : Nat.Prime 2687 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2711 : Nat.Prime 2711 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2789 : Nat.Prime 2789 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2833 : Nat.Prime 2833 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2927 : Nat.Prime 2927 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2971 : Nat.Prime 2971 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3181 : Nat.Prime 3181 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3191 : Nat.Prime 3191 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3209 : Nat.Prime 3209 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3373 : Nat.Prime 3373 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3457 : Nat.Prime 3457 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3463 : Nat.Prime 3463 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3583 : Nat.Prime 3583 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3697 : Nat.Prime 3697 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3769 : Nat.Prime 3769 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3797 : Nat.Prime 3797 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3877 : Nat.Prime 3877 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3989 : Nat.Prime 3989 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4003 : Nat.Prime 4003 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4217 : Nat.Prime 4217 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4231 : Nat.Prime 4231 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4561 : Nat.Prime 4561 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4691 : Nat.Prime 4691 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4813 : Nat.Prime 4813 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4877 : Nat.Prime 4877 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4889 : Nat.Prime 4889 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4909 : Nat.Prime 4909 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4943 : Nat.Prime 4943 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5059 : Nat.Prime 5059 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5413 : Nat.Prime 5413 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5851 : Nat.Prime 5851 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5927 : Nat.Prime 5927 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6053 : Nat.Prime 6053 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6101 : Nat.Prime 6101 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6257 : Nat.Prime 6257 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6469 : Nat.Prime 6469 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6761 : Nat.Prime 6761 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6781 : Nat.Prime 6781 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6997 : Nat.Prime 6997 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7247 : Nat.Prime 7247 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7283 : Nat.Prime 7283 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7349 : Nat.Prime 7349 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7411 : Nat.Prime 7411 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7591 : Nat.Prime 7591 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7649 : Nat.Prime 7649 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8237 : Nat.Prime 8237 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8263 : Nat.Prime 8263 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8317 : Nat.Prime 8317 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8387 : Nat.Prime 8387 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8539 : Nat.Prime 8539 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8629 : Nat.Prime 8629 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8933 : Nat.Prime 8933 := by norm_num

private theorem prime_oneHundredFortyThreeEK_9157 : Nat.Prime 9157 := by norm_num

private theorem prime_oneHundredFortyThreeEK_9413 : Nat.Prime 9413 := by norm_num

private theorem prime_oneHundredFortyThreeEK_9719 : Nat.Prime 9719 := by norm_num

private theorem prime_oneHundredFortyThreeEK_9767 : Nat.Prime 9767 := by norm_num

private theorem prime_oneHundredFortyThreeEK_9781 : Nat.Prime 9781 := by norm_num

private theorem prime_oneHundredFortyThreeEK_11423 : Nat.Prime 11423 := by norm_num

private theorem prime_oneHundredFortyThreeEK_11587 : Nat.Prime 11587 := by norm_num

private theorem prime_oneHundredFortyThreeEK_11953 : Nat.Prime 11953 := by norm_num

private theorem prime_oneHundredFortyThreeEK_12037 : Nat.Prime 12037 := by norm_num

private theorem prime_oneHundredFortyThreeEK_12739 : Nat.Prime 12739 := by norm_num

private theorem prime_oneHundredFortyThreeEK_12959 : Nat.Prime 12959 := by norm_num

private theorem prime_oneHundredFortyThreeEK_13669 : Nat.Prime 13669 := by norm_num

private theorem prime_oneHundredFortyThreeEK_15683 : Nat.Prime 15683 := by norm_num

private theorem prime_oneHundredFortyThreeEK_15797 : Nat.Prime 15797 := by norm_num

private theorem prime_oneHundredFortyThreeEK_16253 : Nat.Prime 16253 := by norm_num

private theorem prime_oneHundredFortyThreeEK_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFortyThreeEK_18539 : Nat.Prime 18539 := by norm_num

private theorem prime_oneHundredFortyThreeEK_18541 : Nat.Prime 18541 := by norm_num

private theorem prime_oneHundredFortyThreeEK_18679 : Nat.Prime 18679 := by norm_num

private theorem prime_oneHundredFortyThreeEK_18797 : Nat.Prime 18797 := by norm_num

private theorem prime_oneHundredFortyThreeEK_20089 : Nat.Prime 20089 := by norm_num

private theorem prime_oneHundredFortyThreeEK_20479 : Nat.Prime 20479 := by norm_num

private theorem prime_oneHundredFortyThreeEK_20611 : Nat.Prime 20611 := by norm_num

private theorem prime_oneHundredFortyThreeEK_20707 : Nat.Prime 20707 := by norm_num

private theorem prime_oneHundredFortyThreeEK_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFortyThreeEK_21617 : Nat.Prime 21617 := by norm_num

private theorem prime_oneHundredFortyThreeEK_21859 : Nat.Prime 21859 := by norm_num

private theorem prime_oneHundredFortyThreeEK_23557 : Nat.Prime 23557 := by norm_num

private theorem prime_oneHundredFortyThreeEK_24107 : Nat.Prime 24107 := by norm_num

private theorem prime_oneHundredFortyThreeEK_25229 : Nat.Prime 25229 := by norm_num

private theorem prime_oneHundredFortyThreeEK_28729 : Nat.Prime 28729 := by norm_num

private theorem prime_oneHundredFortyThreeEK_31547 : Nat.Prime 31547 := by norm_num

private theorem prime_oneHundredFortyThreeEK_32213 : Nat.Prime 32213 := by norm_num

private theorem prime_oneHundredFortyThreeEK_32869 : Nat.Prime 32869 := by norm_num

private theorem prime_oneHundredFortyThreeEK_36293 : Nat.Prime 36293 := by norm_num

private theorem prime_oneHundredFortyThreeEK_36389 : Nat.Prime 36389 := by norm_num

private theorem prime_oneHundredFortyThreeEK_36467 : Nat.Prime 36467 := by norm_num

private theorem prime_oneHundredFortyThreeEK_37337 : Nat.Prime 37337 := by norm_num

private theorem prime_oneHundredFortyThreeEK_39509 : Nat.Prime 39509 := by norm_num

private theorem prime_oneHundredFortyThreeEK_40189 : Nat.Prime 40189 := by norm_num

private theorem prime_oneHundredFortyThreeEK_42281 : Nat.Prime 42281 := by norm_num

private theorem prime_oneHundredFortyThreeEK_43759 : Nat.Prime 43759 := by norm_num

private theorem prime_oneHundredFortyThreeEK_45127 : Nat.Prime 45127 := by norm_num

private theorem prime_oneHundredFortyThreeEK_48527 : Nat.Prime 48527 := by norm_num

private theorem prime_oneHundredFortyThreeEK_49261 : Nat.Prime 49261 := by norm_num

private theorem prime_oneHundredFortyThreeEK_53897 : Nat.Prime 53897 := by norm_num

private theorem prime_oneHundredFortyThreeEK_54367 : Nat.Prime 54367 := by norm_num

private theorem prime_oneHundredFortyThreeEK_54419 : Nat.Prime 54419 := by norm_num

private theorem prime_oneHundredFortyThreeEK_55351 : Nat.Prime 55351 := by norm_num

private theorem prime_oneHundredFortyThreeEK_55411 : Nat.Prime 55411 := by norm_num

private theorem prime_oneHundredFortyThreeEK_55691 : Nat.Prime 55691 := by norm_num

private theorem prime_oneHundredFortyThreeEK_56893 : Nat.Prime 56893 := by norm_num

private theorem prime_oneHundredFortyThreeEK_57653 : Nat.Prime 57653 := by norm_num

private theorem prime_oneHundredFortyThreeEK_57899 : Nat.Prime 57899 := by norm_num

private theorem prime_oneHundredFortyThreeEK_60077 : Nat.Prime 60077 := by norm_num

private theorem prime_oneHundredFortyThreeEK_61471 : Nat.Prime 61471 := by norm_num

private theorem prime_oneHundredFortyThreeEK_65413 : Nat.Prime 65413 := by norm_num

private theorem prime_oneHundredFortyThreeEK_74189 : Nat.Prime 74189 := by norm_num

private theorem prime_oneHundredFortyThreeEK_74381 : Nat.Prime 74381 := by norm_num

private theorem prime_oneHundredFortyThreeEK_77237 : Nat.Prime 77237 := by norm_num

private theorem prime_oneHundredFortyThreeEK_80429 : Nat.Prime 80429 := by norm_num

private theorem prime_oneHundredFortyThreeEK_83207 : Nat.Prime 83207 := by norm_num

private theorem prime_oneHundredFortyThreeEK_86753 : Nat.Prime 86753 := by norm_num

private theorem prime_oneHundredFortyThreeEK_86923 : Nat.Prime 86923 := by norm_num

private theorem prime_oneHundredFortyThreeEK_86969 : Nat.Prime 86969 := by norm_num

private theorem prime_oneHundredFortyThreeEK_87421 : Nat.Prime 87421 := by norm_num

private theorem prime_oneHundredFortyThreeEK_94151 : Nat.Prime 94151 := by norm_num

private theorem prime_oneHundredFortyThreeEK_95317 : Nat.Prime 95317 := by norm_num

private theorem prime_oneHundredFortyThreeEK_96263 : Nat.Prime 96263 := by norm_num

private theorem prime_oneHundredFortyThreeEK_96323 : Nat.Prime 96323 := by norm_num

private theorem prime_oneHundredFortyThreeEK_104579 : Nat.Prime 104579 := by norm_num

private theorem prime_oneHundredFortyThreeEK_106783 : Nat.Prime 106783 := by norm_num

private theorem prime_oneHundredFortyThreeEK_119929 : Nat.Prime 119929 := by norm_num

private theorem prime_oneHundredFortyThreeEK_121931 : Nat.Prime 121931 := by norm_num

private theorem prime_oneHundredFortyThreeEK_125539 : Nat.Prime 125539 := by norm_num

private theorem prime_oneHundredFortyThreeEK_129347 : Nat.Prime 129347 := by norm_num

private theorem prime_oneHundredFortyThreeEK_159319 : Nat.Prime 159319 := by norm_num

private theorem prime_oneHundredFortyThreeEK_160183 : Nat.Prime 160183 := by norm_num

private theorem prime_oneHundredFortyThreeEK_170707 : Nat.Prime 170707 := by norm_num

private theorem prime_oneHundredFortyThreeEK_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFortyThreeEK_172199 : Nat.Prime 172199 := by norm_num

private theorem prime_oneHundredFortyThreeEK_173861 : Nat.Prime 173861 := by norm_num

private theorem prime_oneHundredFortyThreeEK_175727 : Nat.Prime 175727 := by norm_num

private theorem prime_oneHundredFortyThreeEK_179923 : Nat.Prime 179923 := by norm_num

private theorem prime_oneHundredFortyThreeEK_181183 : Nat.Prime 181183 := by norm_num

private theorem prime_oneHundredFortyThreeEK_181439 : Nat.Prime 181439 := by norm_num

private theorem prime_oneHundredFortyThreeEK_185753 : Nat.Prime 185753 := by norm_num

private theorem prime_oneHundredFortyThreeEK_192391 : Nat.Prime 192391 := by norm_num

private theorem prime_oneHundredFortyThreeEK_197807 : Nat.Prime 197807 := by norm_num

private theorem prime_oneHundredFortyThreeEK_199457 : Nat.Prime 199457 := by norm_num

private theorem prime_oneHundredFortyThreeEK_204859 : Nat.Prime 204859 := by norm_num

private theorem prime_oneHundredFortyThreeEK_209497 : Nat.Prime 209497 := by norm_num

private theorem prime_oneHundredFortyThreeEK_210071 : Nat.Prime 210071 := by norm_num

private theorem prime_oneHundredFortyThreeEK_210901 : Nat.Prime 210901 := by norm_num

private theorem prime_oneHundredFortyThreeEK_238531 : Nat.Prime 238531 := by norm_num

private theorem prime_oneHundredFortyThreeEK_251893 : Nat.Prime 251893 := by norm_num

private theorem prime_oneHundredFortyThreeEK_261031 : Nat.Prime 261031 := by norm_num

private theorem prime_oneHundredFortyThreeEK_307169 : Nat.Prime 307169 := by norm_num

private theorem prime_oneHundredFortyThreeEK_321187 : Nat.Prime 321187 := by norm_num

private theorem prime_oneHundredFortyThreeEK_327289 : Nat.Prime 327289 := by norm_num

private theorem prime_oneHundredFortyThreeEK_329473 : Nat.Prime 329473 := by norm_num

private theorem prime_oneHundredFortyThreeEK_338323 : Nat.Prime 338323 := by norm_num

private theorem prime_oneHundredFortyThreeEK_348307 : Nat.Prime 348307 := by norm_num

private theorem prime_oneHundredFortyThreeEK_349483 : Nat.Prime 349483 := by norm_num

private theorem prime_oneHundredFortyThreeEK_356761 : Nat.Prime 356761 := by norm_num

private theorem prime_oneHundredFortyThreeEK_372179 : Nat.Prime 372179 := by norm_num

private theorem prime_oneHundredFortyThreeEK_381443 : Nat.Prime 381443 := by norm_num

private theorem prime_oneHundredFortyThreeEK_381461 : Nat.Prime 381461 := by norm_num

private theorem prime_oneHundredFortyThreeEK_384533 : Nat.Prime 384533 := by norm_num

private theorem prime_oneHundredFortyThreeEK_429101 : Nat.Prime 429101 := by norm_num

private theorem prime_oneHundredFortyThreeEK_436889 : Nat.Prime 436889 := by norm_num

private theorem prime_oneHundredFortyThreeEK_472523 : Nat.Prime 472523 := by norm_num

private theorem prime_oneHundredFortyThreeEK_489913 : Nat.Prime 489913 := by norm_num

private theorem prime_oneHundredFortyThreeEK_526717 : Nat.Prime 526717 := by norm_num

private theorem prime_oneHundredFortyThreeEK_559709 : Nat.Prime 559709 := by norm_num

private theorem prime_oneHundredFortyThreeEK_562621 : Nat.Prime 562621 := by norm_num

private theorem prime_oneHundredFortyThreeEK_646937 : Nat.Prime 646937 := by norm_num

private theorem prime_oneHundredFortyThreeEK_678593 : Nat.Prime 678593 := by norm_num

private theorem prime_oneHundredFortyThreeEK_696743 : Nat.Prime 696743 := by norm_num

private theorem prime_oneHundredFortyThreeEK_710341 : Nat.Prime 710341 := by norm_num

private theorem prime_oneHundredFortyThreeEK_733127 : Nat.Prime 733127 := by norm_num

private theorem prime_oneHundredFortyThreeEK_767537 : Nat.Prime 767537 := by norm_num

private theorem prime_oneHundredFortyThreeEK_792163 : Nat.Prime 792163 := by norm_num

private theorem prime_oneHundredFortyThreeEK_815891 : Nat.Prime 815891 := by norm_num

private theorem prime_oneHundredFortyThreeEK_819827 : Nat.Prime 819827 := by norm_num

private theorem prime_oneHundredFortyThreeEK_835141 : Nat.Prime 835141 := by norm_num

private theorem prime_oneHundredFortyThreeEK_849857 : Nat.Prime 849857 := by norm_num

private theorem prime_oneHundredFortyThreeEK_855947 : Nat.Prime 855947 := by norm_num

private theorem prime_oneHundredFortyThreeEK_872789 : Nat.Prime 872789 := by norm_num

private theorem prime_oneHundredFortyThreeEK_965749 : Nat.Prime 965749 := by norm_num

private theorem prime_oneHundredFortyThreeEK_986837 : Nat.Prime 986837 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1004677 : Nat.Prime 1004677 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1096763 : Nat.Prime 1096763 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1128557 : Nat.Prime 1128557 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1155247 : Nat.Prime 1155247 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1265333 : Nat.Prime 1265333 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1265639 : Nat.Prime 1265639 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1276397 : Nat.Prime 1276397 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1353239 : Nat.Prime 1353239 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1619687 : Nat.Prime 1619687 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1655281 : Nat.Prime 1655281 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1739383 : Nat.Prime 1739383 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1767307 : Nat.Prime 1767307 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1779541 : Nat.Prime 1779541 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1793161 : Nat.Prime 1793161 := by norm_num

private theorem prime_oneHundredFortyThreeEK_1847539 : Nat.Prime 1847539 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2060099 : Nat.Prime 2060099 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2186603 : Nat.Prime 2186603 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2387927 : Nat.Prime 2387927 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2471107 : Nat.Prime 2471107 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2479927 : Nat.Prime 2479927 := by norm_num

private theorem prime_oneHundredFortyThreeEK_2950459 : Nat.Prime 2950459 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3059143 : Nat.Prime 3059143 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3070471 : Nat.Prime 3070471 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3120619 : Nat.Prime 3120619 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3165203 : Nat.Prime 3165203 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3204139 : Nat.Prime 3204139 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3283807 : Nat.Prime 3283807 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3660913 : Nat.Prime 3660913 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3700691 : Nat.Prime 3700691 := by norm_num

private theorem prime_oneHundredFortyThreeEK_3928753 : Nat.Prime 3928753 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4040789 : Nat.Prime 4040789 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4224991 : Nat.Prime 4224991 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4362719 : Nat.Prime 4362719 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4525627 : Nat.Prime 4525627 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4631749 : Nat.Prime 4631749 := by norm_num

private theorem prime_oneHundredFortyThreeEK_4724353 : Nat.Prime 4724353 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5027467 : Nat.Prime 5027467 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5109047 : Nat.Prime 5109047 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5194793 : Nat.Prime 5194793 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5202511 : Nat.Prime 5202511 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5220923 : Nat.Prime 5220923 := by norm_num

private theorem prime_oneHundredFortyThreeEK_5762437 : Nat.Prime 5762437 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6099161 : Nat.Prime 6099161 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6175997 : Nat.Prime 6175997 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6230579 : Nat.Prime 6230579 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6332663 : Nat.Prime 6332663 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6469847 : Nat.Prime 6469847 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6926357 : Nat.Prime 6926357 := by norm_num

private theorem prime_oneHundredFortyThreeEK_6980969 : Nat.Prime 6980969 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7027633 : Nat.Prime 7027633 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7229809 : Nat.Prime 7229809 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7631857 : Nat.Prime 7631857 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7829581 : Nat.Prime 7829581 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7847327 : Nat.Prime 7847327 := by norm_num

private theorem prime_oneHundredFortyThreeEK_7983037 : Nat.Prime 7983037 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8002073 : Nat.Prime 8002073 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8237417 : Nat.Prime 8237417 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8302403 : Nat.Prime 8302403 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8348687 : Nat.Prime 8348687 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8731213 : Nat.Prime 8731213 := by norm_num

private theorem prime_oneHundredFortyThreeEK_8887139 : Nat.Prime 8887139 := by norm_num

private theorem prime_oneHundredFortyThreeEK_9890501 : Nat.Prime 9890501 := by norm_num

private theorem prime_oneHundredFortyThreeEK_10019957 : Nat.Prime 10019957 := by norm_num

private theorem prime_oneHundredFortyThreeEK_10320283 : Nat.Prime 10320283 := by norm_num

private theorem prime_oneHundredFortyThreeEK_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFortyThreeEK_11352647 : Nat.Prime 11352647 := by norm_num

private theorem prime_oneHundredFortyThreeEK_12019589 : Nat.Prime 12019589 := by norm_num

private theorem prime_oneHundredFortyThreeEK_12415027 : Nat.Prime 12415027 := by norm_num

private theorem prime_oneHundredFortyThreeEK_13472059 : Nat.Prime 13472059 := by norm_num

private theorem prime_oneHundredFortyThreeEK_15501823 : Nat.Prime 15501823 := by norm_num

private theorem prime_oneHundredFortyThreeEK_15838369 : Nat.Prime 15838369 := by norm_num

private theorem prime_oneHundredFortyThreeEK_16121527 : Nat.Prime 16121527 := by norm_num

private theorem prime_oneHundredFortyThreeEK_16605997 : Nat.Prime 16605997 := by norm_num

private theorem prime_oneHundredFortyThreeEK_16783901 : Nat.Prime 16783901 := by norm_num

private theorem prime_oneHundredFortyThreeEK_18880633 : Nat.Prime 18880633 := by norm_num

private theorem prime_oneHundredFortyThreeEK_19976597 : Nat.Prime 19976597 := by norm_num

private theorem prime_oneHundredFortyThreeEK_20495581 : Nat.Prime 20495581 := by norm_num

private theorem prime_oneHundredFortyThreeEK_20973863 : Nat.Prime 20973863 := by norm_num

private theorem prime_oneHundredFortyThreeEK_21473623 : Nat.Prime 21473623 := by norm_num

private theorem prime_oneHundredFortyThreeEK_21902921 : Nat.Prime 21902921 := by norm_num

private theorem prime_oneHundredFortyThreeEK_23087123 : Nat.Prime 23087123 := by norm_num

private theorem prime_oneHundredFortyThreeEK_23989367 : Nat.Prime 23989367 := by norm_num

private theorem prime_oneHundredFortyThreeEK_24173603 : Nat.Prime 24173603 := by norm_num

private theorem prime_oneHundredFortyThreeEK_27092657 : Nat.Prime 27092657 := by norm_num

private theorem prime_oneHundredFortyThreeEK_27867643 : Nat.Prime 27867643 := by norm_num

private theorem prime_oneHundredFortyThreeEK_28415539 : Nat.Prime 28415539 := by norm_num

private theorem prime_oneHundredFortyThreeEK_30612443 : Nat.Prime 30612443 := by
  apply lucas_primality 30612443 (2 : ZMod 30612443)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) = 30612443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_2186603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30612443) ^ 15306221 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 4373206 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 14 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_32066569 : Nat.Prime 32066569 := by
  apply lucas_primality 32066569 (7 : ZMod 32066569)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (37, 1), (12037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (37, 1), (12037, 1)] : List FactorBlock).map factorBlockValue).prod) = 32066569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_37
      · exact prime_oneHundredFortyThreeEK_12037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 32066569) ^ 16033284 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 32066569) ^ 10688856 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 32066569) ^ 866664 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 32066569) ^ 2664 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_35389313 : Nat.Prime 35389313 := by
  apply lucas_primality 35389313 (3 : ZMod 35389313)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (127, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (127, 1), (311, 1)] : List FactorBlock).map factorBlockValue).prod) = 35389313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_127
      · exact prime_oneHundredFortyThreeEK_311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35389313) ^ 17694656 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35389313) ^ 5055616 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35389313) ^ 278656 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35389313) ^ 113792 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_39162769 : Nat.Prime 39162769 := by
  apply lucas_primality 39162769 (11 : ZMod 39162769)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (815891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (815891, 1)] : List FactorBlock).map factorBlockValue).prod) = 39162769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_815891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 39162769) ^ 19581384 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 39162769) ^ 13054256 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 39162769) ^ 48 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_42051899 : Nat.Prime 42051899 := by
  apply lucas_primality 42051899 (6 : ZMod 42051899)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (429101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (429101, 1)] : List FactorBlock).map factorBlockValue).prod) = 42051899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_429101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 42051899) ^ 21025949 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 42051899) ^ 6007414 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 42051899) ^ 98 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_43001837 : Nat.Prime 43001837 := by
  apply lucas_primality 43001837 (2 : ZMod 43001837)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) = 43001837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_239
      · exact prime_oneHundredFortyThreeEK_1451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43001837) ^ 21500918 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 1387156 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 179924 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 29636 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_44396689 : Nat.Prime 44396689 := by
  apply lucas_primality 44396689 (23 : ZMod 44396689)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (229, 1), (577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (229, 1), (577, 1)] : List FactorBlock).map factorBlockValue).prod) = 44396689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_229
      · exact prime_oneHundredFortyThreeEK_577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 44396689) ^ 22198344 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (23 : ZMod 44396689) ^ 14798896 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (23 : ZMod 44396689) ^ 6342384 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (23 : ZMod 44396689) ^ 193872 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (23 : ZMod 44396689) ^ 76944 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_48347207 : Nat.Prime 48347207 := by
  apply lucas_primality 48347207 (5 : ZMod 48347207)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (24173603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (24173603, 1)] : List FactorBlock).map factorBlockValue).prod) = 48347207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_24173603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 48347207) ^ 24173603 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 48347207) ^ 2 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_49471423 : Nat.Prime 49471423 := by
  apply lucas_primality 49471423 (3 : ZMod 49471423)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) = 49471423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_8237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49471423) ^ 24735711 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 16490474 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 7067346 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 4497402 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 3805494 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 6006 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_52025111 : Nat.Prime 52025111 := by
  apply lucas_primality 52025111 (13 : ZMod 52025111)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) = 52025111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_5202511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 52025111) ^ 26012555 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10405022 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_75474943 : Nat.Prime 75474943 := by
  apply lucas_primality 75474943 (3 : ZMod 75474943)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (313, 1), (40189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (313, 1), (40189, 1)] : List FactorBlock).map factorBlockValue).prod) = 75474943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_313
      · exact prime_oneHundredFortyThreeEK_40189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75474943) ^ 37737471 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 75474943) ^ 25158314 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 75474943) ^ 241134 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 75474943) ^ 1878 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_75825557 : Nat.Prime 75825557 := by
  apply lucas_primality 75825557 (2 : ZMod 75825557)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (151, 1), (125539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (151, 1), (125539, 1)] : List FactorBlock).map factorBlockValue).prod) = 75825557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_151
      · exact prime_oneHundredFortyThreeEK_125539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75825557) ^ 37912778 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825557) ^ 502156 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 75825557) ^ 604 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_76426429 : Nat.Prime 76426429 := by
  apply lucas_primality 76426429 (10 : ZMod 76426429)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (489913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (489913, 1)] : List FactorBlock).map factorBlockValue).prod) = 76426429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_489913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 76426429) ^ 38213214 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 76426429) ^ 25475476 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 76426429) ^ 5878956 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 76426429) ^ 156 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_78381649 : Nat.Prime 78381649 := by
  apply lucas_primality 78381649 (7 : ZMod 78381649)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (181439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (181439, 1)] : List FactorBlock).map factorBlockValue).prod) = 78381649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_181439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 78381649) ^ 39190824 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 78381649) ^ 26127216 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 78381649) ^ 432 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_81194341 : Nat.Prime 81194341 := by
  apply lucas_primality 81194341 (10 : ZMod 81194341)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1353239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1353239, 1)] : List FactorBlock).map factorBlockValue).prod) = 81194341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_1353239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 81194341) ^ 40597170 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 81194341) ^ 27064780 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 81194341) ^ 16238868 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 81194341) ^ 60 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_96156713 : Nat.Prime 96156713 := by
  apply lucas_primality 96156713 (3 : ZMod 96156713)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (12019589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (12019589, 1)] : List FactorBlock).map factorBlockValue).prod) = 96156713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_12019589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 96156713) ^ 48078356 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 96156713) ^ 8 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_96729163 : Nat.Prime 96729163 := by
  apply lucas_primality 96729163 (3 : ZMod 96729163)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (16121527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (16121527, 1)] : List FactorBlock).map factorBlockValue).prod) = 96729163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_16121527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 96729163) ^ 48364581 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 96729163) ^ 32243054 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 96729163) ^ 6 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_103213379 : Nat.Prime 103213379 := by
  apply lucas_primality 103213379 (2 : ZMod 103213379)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (1779541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (1779541, 1)] : List FactorBlock).map factorBlockValue).prod) = 103213379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_29
      · exact prime_oneHundredFortyThreeEK_1779541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103213379) ^ 51606689 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 103213379) ^ 3559082 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 103213379) ^ 58 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_104050223 : Nat.Prime 104050223 := by
  apply lucas_primality 104050223 (5 : ZMod 104050223)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) = 104050223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_52025111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 104050223) ^ 52025111 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 104050223) ^ 2 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_105338599 : Nat.Prime 105338599 := by
  apply lucas_primality 105338599 (3 : ZMod 105338599)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (947, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (947, 1), (18539, 1)] : List FactorBlock).map factorBlockValue).prod) = 105338599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_947
      · exact prime_oneHundredFortyThreeEK_18539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 105338599) ^ 52669299 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 105338599) ^ 35112866 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 105338599) ^ 111234 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 105338599) ^ 5682 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_130951069 : Nat.Prime 130951069 := by
  apply lucas_primality 130951069 (6 : ZMod 130951069)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (31, 1), (20707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (31, 1), (20707, 1)] : List FactorBlock).map factorBlockValue).prod) = 130951069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_20707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 130951069) ^ 65475534 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 130951069) ^ 43650356 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 130951069) ^ 7703004 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 130951069) ^ 4224228 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 130951069) ^ 6324 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_132193109 : Nat.Prime 132193109 := by
  apply lucas_primality 132193109 (2 : ZMod 132193109)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (1739383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (1739383, 1)] : List FactorBlock).map factorBlockValue).prod) = 132193109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_1739383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 132193109) ^ 66096554 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 132193109) ^ 6957532 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 132193109) ^ 76 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_142641539 : Nat.Prime 142641539 := by
  apply lucas_primality 142641539 (2 : ZMod 142641539)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (238531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (238531, 1)] : List FactorBlock).map factorBlockValue).prod) = 142641539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_23
      · exact prime_oneHundredFortyThreeEK_238531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 142641539) ^ 71320769 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 10972426 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 6201806 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 598 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_143433401 : Nat.Prime 143433401 := by
  apply lucas_primality 143433401 (7 : ZMod 143433401)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 2), (5927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 2), (5927, 1)] : List FactorBlock).map factorBlockValue).prod) = 143433401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_5927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 143433401) ^ 71716700 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 143433401) ^ 28686680 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 143433401) ^ 13039400 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 143433401) ^ 24200 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_151498199 : Nat.Prime 151498199 := by
  apply lucas_primality 151498199 (13 : ZMod 151498199)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (1847539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (1847539, 1)] : List FactorBlock).map factorBlockValue).prod) = 151498199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_41
      · exact prime_oneHundredFortyThreeEK_1847539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 151498199) ^ 75749099 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (13 : ZMod 151498199) ^ 3695078 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (13 : ZMod 151498199) ^ 82 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_160041461 : Nat.Prime 160041461 := by
  apply lucas_primality 160041461 (2 : ZMod 160041461)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (8002073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (8002073, 1)] : List FactorBlock).map factorBlockValue).prod) = 160041461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_8002073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 160041461) ^ 80020730 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160041461) ^ 32008292 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 160041461) ^ 20 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_161211241 : Nat.Prime 161211241 := by
  apply lucas_primality 161211241 (17 : ZMod 161211241)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (431, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (431, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) = 161211241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_431
      · exact prime_oneHundredFortyThreeEK_1039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 161211241) ^ 80605620 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (17 : ZMod 161211241) ^ 53737080 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (17 : ZMod 161211241) ^ 32242248 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (17 : ZMod 161211241) ^ 374040 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (17 : ZMod 161211241) ^ 155160 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_162186439 : Nat.Prime 162186439 := by
  apply lucas_primality 162186439 (3 : ZMod 162186439)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (599, 1), (45127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (599, 1), (45127, 1)] : List FactorBlock).map factorBlockValue).prod) = 162186439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_599
      · exact prime_oneHundredFortyThreeEK_45127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 162186439) ^ 81093219 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 162186439) ^ 54062146 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 162186439) ^ 270762 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 162186439) ^ 3594 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_164976709 : Nat.Prime 164976709 := by
  apply lucas_primality 164976709 (2 : ZMod 164976709)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (29, 1), (36467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (29, 1), (36467, 1)] : List FactorBlock).map factorBlockValue).prod) = 164976709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_29
      · exact prime_oneHundredFortyThreeEK_36467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 164976709) ^ 82488354 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 164976709) ^ 54992236 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 164976709) ^ 12690516 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 164976709) ^ 5688852 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 164976709) ^ 4524 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_185423809 : Nat.Prime 185423809 := by
  apply lucas_primality 185423809 (11 : ZMod 185423809)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) = 185423809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_965749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 185423809) ^ 92711904 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 61807936 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 192 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_189328049 : Nat.Prime 189328049 := by
  apply lucas_primality 189328049 (3 : ZMod 189328049)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 1), (17, 1), (7649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 1), (17, 1), (7649, 1)] : List FactorBlock).map factorBlockValue).prod) = 189328049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_7649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 189328049) ^ 94664024 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 189328049) ^ 27046864 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 189328049) ^ 14563696 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 189328049) ^ 11136944 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 189328049) ^ 24752 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_192313427 : Nat.Prime 192313427 := by
  apply lucas_primality 192313427 (2 : ZMod 192313427)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (96156713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (96156713, 1)] : List FactorBlock).map factorBlockValue).prod) = 192313427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_96156713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 192313427) ^ 96156713 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 192313427) ^ 2 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_200272519 : Nat.Prime 200272519 := by
  apply lucas_primality 200272519 (15 : ZMod 200272519)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) = 200272519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_181
      · exact prime_oneHundredFortyThreeEK_61471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 200272519) ^ 100136259 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 66757506 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 1106478 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 3258 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_222305873 : Nat.Prime 222305873 := by
  apply lucas_primality 222305873 (5 : ZMod 222305873)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (43, 1), (83, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (43, 1), (83, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) = 222305873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_43
      · exact prime_oneHundredFortyThreeEK_83
      · exact prime_oneHundredFortyThreeEK_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 222305873) ^ 111152936 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 222305873) ^ 13076816 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 222305873) ^ 5169904 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 222305873) ^ 2678384 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 222305873) ^ 970768 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_248942081 : Nat.Prime 248942081 := by
  apply lucas_primality 248942081 (6 : ZMod 248942081)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (5, 1), (47, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (5, 1), (47, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod) = 248942081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_47
      · exact prime_oneHundredFortyThreeEK_2069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 248942081) ^ 124471040 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 248942081) ^ 49788416 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 248942081) ^ 5296640 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 248942081) ^ 120320 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_285551953 : Nat.Prime 285551953 := by
  apply lucas_primality 285551953 (15 : ZMod 285551953)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (849857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (849857, 1)] : List FactorBlock).map factorBlockValue).prod) = 285551953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_849857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 285551953) ^ 142775976 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 285551953) ^ 95183984 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 285551953) ^ 40793136 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 285551953) ^ 336 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_294354029 : Nat.Prime 294354029 := by
  apply lucas_primality 294354029 (2 : ZMod 294354029)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (409, 1), (179923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (409, 1), (179923, 1)] : List FactorBlock).map factorBlockValue).prod) = 294354029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_409
      · exact prime_oneHundredFortyThreeEK_179923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 294354029) ^ 147177014 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 294354029) ^ 719692 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 294354029) ^ 1636 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_316865201 : Nat.Prime 316865201 := by
  apply lucas_primality 316865201 (15 : ZMod 316865201)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (792163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (792163, 1)] : List FactorBlock).map factorBlockValue).prod) = 316865201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_792163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 316865201) ^ 158432600 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 316865201) ^ 63373040 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 316865201) ^ 400 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_349996873 : Nat.Prime 349996873 := by
  apply lucas_primality 349996873 (11 : ZMod 349996873)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) = 349996873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_767537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 349996873) ^ 174998436 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 116665624 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 18420888 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 456 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_362856757 : Nat.Prime 362856757 := by
  apply lucas_primality 362856757 (2 : ZMod 362856757)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (983, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (983, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) = 362856757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_983
      · exact prime_oneHundredFortyThreeEK_1619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 362856757) ^ 181428378 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 362856757) ^ 120952252 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 362856757) ^ 19097724 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 362856757) ^ 369132 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 362856757) ^ 224124 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_378656099 : Nat.Prime 378656099 := by
  apply lucas_primality 378656099 (2 : ZMod 378656099)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (189328049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (189328049, 1)] : List FactorBlock).map factorBlockValue).prod) = 378656099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_189328049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 378656099) ^ 189328049 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 378656099) ^ 2 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_380678593 : Nat.Prime 380678593 := by
  apply lucas_primality 380678593 (19 : ZMod 380678593)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (29, 1), (9767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (29, 1), (9767, 1)] : List FactorBlock).map factorBlockValue).prod) = 380678593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_29
      · exact prime_oneHundredFortyThreeEK_9767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 380678593) ^ 190339296 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (19 : ZMod 380678593) ^ 126892864 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (19 : ZMod 380678593) ^ 54382656 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (19 : ZMod 380678593) ^ 13126848 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (19 : ZMod 380678593) ^ 38976 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_386916653 : Nat.Prime 386916653 := by
  apply lucas_primality 386916653 (2 : ZMod 386916653)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (96729163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (96729163, 1)] : List FactorBlock).map factorBlockValue).prod) = 386916653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_96729163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 386916653) ^ 193458326 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 386916653) ^ 4 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_391466479 : Nat.Prime 391466479 := by
  apply lucas_primality 391466479 (6 : ZMod 391466479)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (47, 1), (106783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (47, 1), (106783, 1)] : List FactorBlock).map factorBlockValue).prod) = 391466479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_47
      · exact prime_oneHundredFortyThreeEK_106783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 391466479) ^ 195733239 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 391466479) ^ 130488826 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 391466479) ^ 30112806 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 391466479) ^ 8329074 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 391466479) ^ 3666 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_400396429 : Nat.Prime 400396429 := by
  apply lucas_primality 400396429 (2 : ZMod 400396429)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1823, 1), (6101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1823, 1), (6101, 1)] : List FactorBlock).map factorBlockValue).prod) = 400396429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_1823
      · exact prime_oneHundredFortyThreeEK_6101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 400396429) ^ 200198214 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 400396429) ^ 133465476 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 400396429) ^ 219636 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 400396429) ^ 65628 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_416336153 : Nat.Prime 416336153 := by
  apply lucas_primality 416336153 (3 : ZMod 416336153)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47, 1), (347, 1), (3191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47, 1), (347, 1), (3191, 1)] : List FactorBlock).map factorBlockValue).prod) = 416336153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_47
      · exact prime_oneHundredFortyThreeEK_347
      · exact prime_oneHundredFortyThreeEK_3191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 416336153) ^ 208168076 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 416336153) ^ 8858216 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 416336153) ^ 1199816 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 416336153) ^ 130472 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_429543953 : Nat.Prime 429543953 := by
  apply lucas_primality 429543953 (3 : ZMod 429543953)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) = 429543953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_23
      · exact prime_oneHundredFortyThreeEK_37
      · exact prime_oneHundredFortyThreeEK_31547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 429543953) ^ 214771976 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 18675824 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 11609296 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 13616 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_444611747 : Nat.Prime 444611747 := by
  apply lucas_primality 444611747 (2 : ZMod 444611747)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (222305873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (222305873, 1)] : List FactorBlock).map factorBlockValue).prod) = 444611747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_222305873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 444611747) ^ 222305873 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 444611747) ^ 2 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_452849659 : Nat.Prime 452849659 := by
  apply lucas_primality 452849659 (3 : ZMod 452849659)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (75474943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (75474943, 1)] : List FactorBlock).map factorBlockValue).prod) = 452849659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_75474943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 452849659) ^ 226424829 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 452849659) ^ 150949886 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 452849659) ^ 6 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_458601821 : Nat.Prime 458601821 := by
  apply lucas_primality 458601821 (2 : ZMod 458601821)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1049, 1), (21859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1049, 1), (21859, 1)] : List FactorBlock).map factorBlockValue).prod) = 458601821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_1049
      · exact prime_oneHundredFortyThreeEK_21859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 458601821) ^ 229300910 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 458601821) ^ 91720364 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 458601821) ^ 437180 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 458601821) ^ 20980 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_489141011 : Nat.Prime 489141011 := by
  apply lucas_primality 489141011 (2 : ZMod 489141011)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (373, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (373, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) = 489141011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_71
      · exact prime_oneHundredFortyThreeEK_373
      · exact prime_oneHundredFortyThreeEK_1847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 489141011) ^ 244570505 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 489141011) ^ 97828202 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 489141011) ^ 6889310 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 489141011) ^ 1311370 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 489141011) ^ 264830 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_501819427 : Nat.Prime 501819427 := by
  apply lucas_primality 501819427 (2 : ZMod 501819427)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (59, 1), (472523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (59, 1), (472523, 1)] : List FactorBlock).map factorBlockValue).prod) = 501819427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_59
      · exact prime_oneHundredFortyThreeEK_472523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 501819427) ^ 250909713 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 501819427) ^ 167273142 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 501819427) ^ 8505414 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 501819427) ^ 1062 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_544894729 : Nat.Prime 544894729 := by
  apply lucas_primality 544894729 (26 : ZMod 544894729)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (1319, 1), (2459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (1319, 1), (2459, 1)] : List FactorBlock).map factorBlockValue).prod) = 544894729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_1319
      · exact prime_oneHundredFortyThreeEK_2459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 544894729) ^ 272447364 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (26 : ZMod 544894729) ^ 181631576 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (26 : ZMod 544894729) ^ 77842104 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (26 : ZMod 544894729) ^ 413112 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (26 : ZMod 544894729) ^ 221592 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_559010483 : Nat.Prime 559010483 := by
  apply lucas_primality 559010483 (2 : ZMod 559010483)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (1709, 1), (3989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (1709, 1), (3989, 1)] : List FactorBlock).map factorBlockValue).prod) = 559010483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_41
      · exact prime_oneHundredFortyThreeEK_1709
      · exact prime_oneHundredFortyThreeEK_3989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 559010483) ^ 279505241 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 559010483) ^ 13634402 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 559010483) ^ 327098 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 559010483) ^ 140138 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_577198243 : Nat.Prime 577198243 := by
  apply lucas_primality 577198243 (2 : ZMod 577198243)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (32066569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (32066569, 1)] : List FactorBlock).map factorBlockValue).prod) = 577198243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_32066569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 577198243) ^ 288599121 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 577198243) ^ 192399414 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 577198243) ^ 18 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_588708059 : Nat.Prime 588708059 := by
  apply lucas_primality 588708059 (2 : ZMod 588708059)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (294354029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (294354029, 1)] : List FactorBlock).map factorBlockValue).prod) = 588708059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_294354029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 588708059) ^ 294354029 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 588708059) ^ 2 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_625954169 : Nat.Prime 625954169 := by
  apply lucas_primality 625954169 (3 : ZMod 625954169)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (53, 1), (210901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (53, 1), (210901, 1)] : List FactorBlock).map factorBlockValue).prod) = 625954169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_53
      · exact prime_oneHundredFortyThreeEK_210901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 625954169) ^ 312977084 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 625954169) ^ 89422024 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 625954169) ^ 11810456 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 625954169) ^ 2968 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_654336799 : Nat.Prime 654336799 := by
  apply lucas_primality 654336799 (15 : ZMod 654336799)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1223, 1), (3877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1223, 1), (3877, 1)] : List FactorBlock).map factorBlockValue).prod) = 654336799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_23
      · exact prime_oneHundredFortyThreeEK_1223
      · exact prime_oneHundredFortyThreeEK_3877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 654336799) ^ 327168399 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 654336799) ^ 218112266 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 654336799) ^ 28449426 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 654336799) ^ 535026 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (15 : ZMod 654336799) ^ 168774 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_17203
      · exact prime_oneHundredFortyThreeEK_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_837668023 : Nat.Prime 837668023 := by
  apply lucas_primality 837668023 (3 : ZMod 837668023)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1597, 1), (87421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1597, 1), (87421, 1)] : List FactorBlock).map factorBlockValue).prod) = 837668023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_1597
      · exact prime_oneHundredFortyThreeEK_87421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 837668023) ^ 418834011 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 837668023) ^ 279222674 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 837668023) ^ 524526 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 837668023) ^ 9582 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_939065539 : Nat.Prime 939065539 := by
  apply lucas_primality 939065539 (2 : ZMod 939065539)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (8237417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (8237417, 1)] : List FactorBlock).map factorBlockValue).prod) = 939065539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_8237417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 939065539) ^ 469532769 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 939065539) ^ 313021846 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 939065539) ^ 49424502 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 939065539) ^ 114 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1192706971 : Nat.Prime 1192706971 := by
  apply lucas_primality 1192706971 (2 : ZMod 1192706971)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (436889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (436889, 1)] : List FactorBlock).map factorBlockValue).prod) = 1192706971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_436889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1192706971) ^ 596353485 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1192706971) ^ 397568990 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1192706971) ^ 238541394 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1192706971) ^ 170386710 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1192706971) ^ 91746690 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1192706971) ^ 2730 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1199468351 : Nat.Prime 1199468351 := by
  apply lucas_primality 1199468351 (7 : ZMod 1199468351)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (23989367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (23989367, 1)] : List FactorBlock).map factorBlockValue).prod) = 1199468351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_23989367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1199468351) ^ 599734175 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1199468351) ^ 239893670 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 1199468351) ^ 50 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1237593419 : Nat.Prime 1237593419 := by
  apply lucas_primality 1237593419 (2 : ZMod 1237593419)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (1907, 1), (2477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (1907, 1), (2477, 1)] : List FactorBlock).map factorBlockValue).prod) = 1237593419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_131
      · exact prime_oneHundredFortyThreeEK_1907
      · exact prime_oneHundredFortyThreeEK_2477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1237593419) ^ 618796709 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1237593419) ^ 9447278 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1237593419) ^ 648974 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1237593419) ^ 499634 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1398517567 : Nat.Prime 1398517567 := by
  apply lucas_primality 1398517567 (3 : ZMod 1398517567)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (2950459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (2950459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1398517567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_79
      · exact prime_oneHundredFortyThreeEK_2950459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1398517567) ^ 699258783 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398517567) ^ 466172522 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398517567) ^ 17702754 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1398517567) ^ 474 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1470847129 : Nat.Prime 1470847129 := by
  apply lucas_primality 1470847129 (13 : ZMod 1470847129)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (61, 1), (1004677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (61, 1), (1004677, 1)] : List FactorBlock).map factorBlockValue).prod) = 1470847129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_61
      · exact prime_oneHundredFortyThreeEK_1004677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1470847129) ^ 735423564 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1470847129) ^ 490282376 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1470847129) ^ 24112248 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (13 : ZMod 1470847129) ^ 1464 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1750801123 : Nat.Prime 1750801123 := by
  apply lucas_primality 1750801123 (3 : ZMod 1750801123)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (4631749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (4631749, 1)] : List FactorBlock).map factorBlockValue).prod) = 1750801123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_4631749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1750801123) ^ 875400561 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1750801123) ^ 583600374 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1750801123) ^ 250114446 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1750801123) ^ 378 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1808602639 : Nat.Prime 1808602639 := by
  apply lucas_primality 1808602639 (3 : ZMod 1808602639)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (5109047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (5109047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1808602639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_59
      · exact prime_oneHundredFortyThreeEK_5109047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1808602639) ^ 904301319 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1808602639) ^ 602867546 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1808602639) ^ 30654282 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1808602639) ^ 354 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1902115487 : Nat.Prime 1902115487 := by
  apply lucas_primality 1902115487 (5 : ZMod 1902115487)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (1567, 1), (6257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (1567, 1), (6257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1902115487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_97
      · exact prime_oneHundredFortyThreeEK_1567
      · exact prime_oneHundredFortyThreeEK_6257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1902115487) ^ 951057743 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1902115487) ^ 19609438 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1902115487) ^ 1213858 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1902115487) ^ 303998 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1904583937 : Nat.Prime 1904583937 := by
  apply lucas_primality 1904583937 (10 : ZMod 1904583937)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (2479927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (2479927, 1)] : List FactorBlock).map factorBlockValue).prod) = 1904583937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_2479927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 1904583937) ^ 952291968 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 1904583937) ^ 634861312 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 1904583937) ^ 768 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2318099881 : Nat.Prime 2318099881 := by
  apply lucas_primality 2318099881 (7 : ZMod 2318099881)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (349, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (349, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2318099881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_349
      · exact prime_oneHundredFortyThreeEK_55351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2318099881) ^ 1159049940 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 772699960 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 463619976 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 6642120 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 41880 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2686553917 : Nat.Prime 2686553917 := by
  apply lucas_primality 2686553917 (5 : ZMod 2686553917)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (1063, 1), (9157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (1063, 1), (9157, 1)] : List FactorBlock).map factorBlockValue).prod) = 2686553917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_23
      · exact prime_oneHundredFortyThreeEK_1063
      · exact prime_oneHundredFortyThreeEK_9157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2686553917) ^ 1343276958 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2686553917) ^ 895517972 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2686553917) ^ 116806692 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2686553917) ^ 2527332 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2686553917) ^ 293388 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2934846067 : Nat.Prime 2934846067 := by
  apply lucas_primality 2934846067 (3 : ZMod 2934846067)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (489141011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (489141011, 1)] : List FactorBlock).map factorBlockValue).prod) = 2934846067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_489141011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2934846067) ^ 1467423033 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2934846067) ^ 978282022 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2934846067) ^ 6 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_3014317637 : Nat.Prime 3014317637 := by
  apply lucas_primality 3014317637 (2 : ZMod 3014317637)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (1277, 1), (4877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (1277, 1), (4877, 1)] : List FactorBlock).map factorBlockValue).prod) = 3014317637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_1277
      · exact prime_oneHundredFortyThreeEK_4877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3014317637) ^ 1507158818 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014317637) ^ 274028876 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014317637) ^ 2360468 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014317637) ^ 618068 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_3160157971 : Nat.Prime 3160157971 := by
  apply lucas_primality 3160157971 (3 : ZMod 3160157971)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (105338599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (105338599, 1)] : List FactorBlock).map factorBlockValue).prod) = 3160157971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_105338599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3160157971) ^ 1580078985 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3160157971) ^ 1053385990 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3160157971) ^ 632031594 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 3160157971) ^ 30 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_3200829221 : Nat.Prime 3200829221 := by
  apply lucas_primality 3200829221 (10 : ZMod 3200829221)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (160041461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (160041461, 1)] : List FactorBlock).map factorBlockValue).prod) = 3200829221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_160041461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 3200829221) ^ 1600414610 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3200829221) ^ 640165844 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 3200829221) ^ 20 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_3886985953 : Nat.Prime 3886985953 := by
  apply lucas_primality 3886985953 (5 : ZMod 3886985953)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (19, 1), (710341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (19, 1), (710341, 1)] : List FactorBlock).map factorBlockValue).prod) = 3886985953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_710341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3886985953) ^ 1943492976 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3886985953) ^ 1295661984 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3886985953) ^ 204578208 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3886985953) ^ 5472 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_4026981697 : Nat.Prime 4026981697 := by
  apply lucas_primality 4026981697 (10 : ZMod 4026981697)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (20973863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (20973863, 1)] : List FactorBlock).map factorBlockValue).prod) = 4026981697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_20973863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 4026981697) ^ 2013490848 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 4026981697) ^ 1342327232 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 4026981697) ^ 192 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_4205360833 : Nat.Prime 4205360833 := by
  apply lucas_primality 4205360833 (5 : ZMod 4205360833)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (21902921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (21902921, 1)] : List FactorBlock).map factorBlockValue).prod) = 4205360833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_21902921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4205360833) ^ 2102680416 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4205360833) ^ 1401786944 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 4205360833) ^ 192 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_4801947119 : Nat.Prime 4801947119 := by
  apply lucas_primality 4801947119 (7 : ZMod 4801947119)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (89, 1), (409, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (89, 1), (409, 1), (929, 1)] : List FactorBlock).map factorBlockValue).prod) = 4801947119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_71
      · exact prime_oneHundredFortyThreeEK_89
      · exact prime_oneHundredFortyThreeEK_409
      · exact prime_oneHundredFortyThreeEK_929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4801947119) ^ 2400973559 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4801947119) ^ 67633058 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4801947119) ^ 53954462 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4801947119) ^ 11740702 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 4801947119) ^ 5168942 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_4914242863 : Nat.Prime 4914242863 := by
  apply lucas_primality 4914242863 (3 : ZMod 4914242863)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (19976597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (19976597, 1)] : List FactorBlock).map factorBlockValue).prod) = 4914242863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_41
      · exact prime_oneHundredFortyThreeEK_19976597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4914242863) ^ 2457121431 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 1638080954 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 119859582 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 246 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_5129457031 : Nat.Prime 5129457031 := by
  apply lucas_primality 5129457031 (3 : ZMod 5129457031)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (6332663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (6332663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5129457031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_6332663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5129457031) ^ 2564728515 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5129457031) ^ 1709819010 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5129457031) ^ 1025891406 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5129457031) ^ 810 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_5429792839 : Nat.Prime 5429792839 := by
  apply lucas_primality 5429792839 (6 : ZMod 5429792839)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) = 5429792839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_709
      · exact prime_oneHundredFortyThreeEK_1276397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5429792839) ^ 2714896419 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 1809930946 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 7658382 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 4254 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_5444978771 : Nat.Prime 5444978771 := by
  apply lucas_primality 5444978771 (2 : ZMod 5444978771)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (19, 1), (372179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (19, 1), (372179, 1)] : List FactorBlock).map factorBlockValue).prod) = 5444978771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_372179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5444978771) ^ 2722489385 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5444978771) ^ 1088995754 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5444978771) ^ 777854110 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5444978771) ^ 494998070 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5444978771) ^ 286577830 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5444978771) ^ 14630 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_5600598239 : Nat.Prime 5600598239 := by
  apply lucas_primality 5600598239 (11 : ZMod 5600598239)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (557, 1), (5027467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (557, 1), (5027467, 1)] : List FactorBlock).map factorBlockValue).prod) = 5600598239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_557
      · exact prime_oneHundredFortyThreeEK_5027467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 5600598239) ^ 2800299119 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5600598239) ^ 10054934 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 5600598239) ^ 1114 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_5678469211 : Nat.Prime 5678469211 := by
  apply lucas_primality 5678469211 (3 : ZMod 5678469211)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1019, 1), (185753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1019, 1), (185753, 1)] : List FactorBlock).map factorBlockValue).prod) = 5678469211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_1019
      · exact prime_oneHundredFortyThreeEK_185753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5678469211) ^ 2839234605 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5678469211) ^ 1892823070 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5678469211) ^ 1135693842 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5678469211) ^ 5572590 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5678469211) ^ 30570 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_5924881639 : Nat.Prime 5924881639 := by
  apply lucas_primality 5924881639 (3 : ZMod 5924881639)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (97, 1), (261031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (97, 1), (261031, 1)] : List FactorBlock).map factorBlockValue).prod) = 5924881639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_97
      · exact prime_oneHundredFortyThreeEK_261031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5924881639) ^ 2962440819 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5924881639) ^ 1974960546 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5924881639) ^ 455760126 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5924881639) ^ 61081254 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5924881639) ^ 22698 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_5994518779 : Nat.Prime 5994518779 := by
  apply lucas_primality 5994518779 (3 : ZMod 5994518779)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (577, 1), (192391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (577, 1), (192391, 1)] : List FactorBlock).map factorBlockValue).prod) = 5994518779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_577
      · exact prime_oneHundredFortyThreeEK_192391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5994518779) ^ 2997259389 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5994518779) ^ 1998172926 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5994518779) ^ 10389114 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 5994518779) ^ 31158 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_6630942709 : Nat.Prime 6630942709 := by
  apply lucas_primality 6630942709 (6 : ZMod 6630942709)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (83, 1), (170707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (83, 1), (170707, 1)] : List FactorBlock).map factorBlockValue).prod) = 6630942709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_83
      · exact prime_oneHundredFortyThreeEK_170707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6630942709) ^ 3315471354 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 6630942709) ^ 2210314236 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 6630942709) ^ 510072516 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 6630942709) ^ 79890876 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 6630942709) ^ 38844 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_6998309863 : Nat.Prime 6998309863 := by
  apply lucas_primality 6998309863 (3 : ZMod 6998309863)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) = 6998309863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_67
      · exact prime_oneHundredFortyThreeEK_53897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6998309863) ^ 3499154931 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 2332769954 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 411665286 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 368332098 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 104452386 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 129846 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_7146931927 : Nat.Prime 7146931927 := by
  apply lucas_primality 7146931927 (3 : ZMod 7146931927)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (179, 1), (1459, 1), (4561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (179, 1), (1459, 1), (4561, 1)] : List FactorBlock).map factorBlockValue).prod) = 7146931927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_179
      · exact prime_oneHundredFortyThreeEK_1459
      · exact prime_oneHundredFortyThreeEK_4561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7146931927) ^ 3573465963 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 7146931927) ^ 2382310642 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 7146931927) ^ 39926994 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 7146931927) ^ 4898514 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 7146931927) ^ 1566966 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_7826146763 : Nat.Prime 7826146763 := by
  apply lucas_primality 7826146763 (6 : ZMod 7826146763)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (559010483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (559010483, 1)] : List FactorBlock).map factorBlockValue).prod) = 7826146763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_559010483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 7826146763) ^ 3913073381 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7826146763) ^ 1118020966 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 7826146763) ^ 14 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_7902610643 : Nat.Prime 7902610643 := by
  apply lucas_primality 7902610643 (2 : ZMod 7902610643)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (44396689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (44396689, 1)] : List FactorBlock).map factorBlockValue).prod) = 7902610643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_89
      · exact prime_oneHundredFortyThreeEK_44396689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7902610643) ^ 3951305321 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7902610643) ^ 88793378 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 7902610643) ^ 178 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_8831675711 : Nat.Prime 8831675711 := by
  apply lucas_primality 8831675711 (22 : ZMod 8831675711)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (6175997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (6175997, 1)] : List FactorBlock).map factorBlockValue).prod) = 8831675711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_6175997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 8831675711) ^ 4415837855 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (22 : ZMod 8831675711) ^ 1766335142 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (22 : ZMod 8831675711) ^ 802879610 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (22 : ZMod 8831675711) ^ 679359670 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (22 : ZMod 8831675711) ^ 1430 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_9020032543 : Nat.Prime 9020032543 := by
  apply lucas_primality 9020032543 (6 : ZMod 9020032543)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (293, 1), (36389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (293, 1), (36389, 1)] : List FactorBlock).map factorBlockValue).prod) = 9020032543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_47
      · exact prime_oneHundredFortyThreeEK_293
      · exact prime_oneHundredFortyThreeEK_36389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9020032543) ^ 4510016271 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 9020032543) ^ 3006677514 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 9020032543) ^ 191915586 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 9020032543) ^ 30785094 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 9020032543) ^ 247878 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_9257508937 : Nat.Prime 9257508937 := by
  apply lucas_primality 9257508937 (5 : ZMod 9257508937)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) = 9257508937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_9890501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9257508937) ^ 4628754468 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 3085836312 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 712116072 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 936 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_10702916611 : Nat.Prime 10702916611 := by
  apply lucas_primality 10702916611 (7 : ZMod 10702916611)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (29, 1), (47, 1), (89, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (29, 1), (47, 1), (89, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) = 10702916611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_29
      · exact prime_oneHundredFortyThreeEK_47
      · exact prime_oneHundredFortyThreeEK_89
      · exact prime_oneHundredFortyThreeEK_173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10702916611) ^ 5351458305 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10702916611) ^ 3567638870 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10702916611) ^ 2140583322 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10702916611) ^ 629583330 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10702916611) ^ 369066090 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10702916611) ^ 227721630 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10702916611) ^ 120257490 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 10702916611) ^ 61866570 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_12383928439 : Nat.Prime 12383928439 := by
  apply lucas_primality 12383928439 (3 : ZMod 12383928439)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (773, 1), (381443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (773, 1), (381443, 1)] : List FactorBlock).map factorBlockValue).prod) = 12383928439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_773
      · exact prime_oneHundredFortyThreeEK_381443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12383928439) ^ 6191964219 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 12383928439) ^ 4127976146 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 12383928439) ^ 1769132634 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 12383928439) ^ 16020606 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 12383928439) ^ 32466 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_12886318591 : Nat.Prime 12886318591 := by
  apply lucas_primality 12886318591 (6 : ZMod 12886318591)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) = 12886318591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_429543953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 12886318591) ^ 6443159295 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 4295439530 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 2577263718 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 30 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_17348290783 : Nat.Prime 17348290783 := by
  apply lucas_primality 17348290783 (3 : ZMod 17348290783)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9413, 1), (307169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9413, 1), (307169, 1)] : List FactorBlock).map factorBlockValue).prod) = 17348290783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_9413
      · exact prime_oneHundredFortyThreeEK_307169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17348290783) ^ 8674145391 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 17348290783) ^ 5782763594 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 17348290783) ^ 1843014 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 17348290783) ^ 56478 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_17901381821 : Nat.Prime 17901381821 := by
  apply lucas_primality 17901381821 (3 : ZMod 17901381821)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (17, 1), (769, 1), (9781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (17, 1), (769, 1), (9781, 1)] : List FactorBlock).map factorBlockValue).prod) = 17901381821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_769
      · exact prime_oneHundredFortyThreeEK_9781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17901381821) ^ 8950690910 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 17901381821) ^ 3580276364 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 17901381821) ^ 2557340260 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 17901381821) ^ 1053022460 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 17901381821) ^ 23278780 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 17901381821) ^ 1830220 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_19083311537 : Nat.Prime 19083311537 := by
  apply lucas_primality 19083311537 (3 : ZMod 19083311537)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1192706971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1192706971, 1)] : List FactorBlock).map factorBlockValue).prod) = 19083311537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_1192706971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 19083311537) ^ 9541655768 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 19083311537) ^ 16 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_19417482319 : Nat.Prime 19417482319 := by
  apply lucas_primality 19417482319 (6 : ZMod 19417482319)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (248942081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (248942081, 1)] : List FactorBlock).map factorBlockValue).prod) = 19417482319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_248942081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 19417482319) ^ 9708741159 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 19417482319) ^ 6472494106 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 19417482319) ^ 1493652486 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 19417482319) ^ 78 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_20544302087 : Nat.Prime 20544302087 := by
  apply lucas_primality 20544302087 (5 : ZMod 20544302087)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (17, 1), (7847327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (17, 1), (7847327, 1)] : List FactorBlock).map factorBlockValue).prod) = 20544302087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_7847327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 20544302087) ^ 10272151043 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 20544302087) ^ 2934900298 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 20544302087) ^ 1867663826 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 20544302087) ^ 1208488358 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 20544302087) ^ 2618 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_21922472071 : Nat.Prime 21922472071 := by
  apply lucas_primality 21922472071 (3 : ZMod 21922472071)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (81194341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (81194341, 1)] : List FactorBlock).map factorBlockValue).prod) = 21922472071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_81194341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 21922472071) ^ 10961236035 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 21922472071) ^ 7307490690 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 21922472071) ^ 4384494414 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 21922472071) ^ 270 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_22292713759 : Nat.Prime 22292713759 := by
  apply lucas_primality 22292713759 (7 : ZMod 22292713759)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (75825557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (75825557, 1)] : List FactorBlock).map factorBlockValue).prod) = 22292713759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_75825557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 22292713759) ^ 11146356879 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 7430904586 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 3184673394 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 22292713759) ^ 294 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_26177599013 : Nat.Prime 26177599013 := by
  apply lucas_primality 26177599013 (2 : ZMod 26177599013)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (37, 1), (6099161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (37, 1), (6099161, 1)] : List FactorBlock).map factorBlockValue).prod) = 26177599013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_29
      · exact prime_oneHundredFortyThreeEK_37
      · exact prime_oneHundredFortyThreeEK_6099161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26177599013) ^ 13088799506 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 26177599013) ^ 902675828 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 26177599013) ^ 707502676 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 26177599013) ^ 4292 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_27918548017 : Nat.Prime 27918548017 := by
  apply lucas_primality 27918548017 (5 : ZMod 27918548017)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) = 27918548017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_30612443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27918548017) ^ 13959274008 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 9306182672 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 1469397264 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 912 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_29485457179 : Nat.Prime 29485457179 := by
  apply lucas_primality 29485457179 (2 : ZMod 29485457179)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4914242863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4914242863, 1)] : List FactorBlock).map factorBlockValue).prod) = 29485457179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_4914242863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29485457179) ^ 14742728589 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29485457179) ^ 9828485726 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 29485457179) ^ 6 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_35160493427 : Nat.Prime 35160493427 := by
  apply lucas_primality 35160493427 (2 : ZMod 35160493427)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (269, 1), (2711, 1), (24107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (269, 1), (2711, 1), (24107, 1)] : List FactorBlock).map factorBlockValue).prod) = 35160493427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_269
      · exact prime_oneHundredFortyThreeEK_2711
      · exact prime_oneHundredFortyThreeEK_24107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35160493427) ^ 17580246713 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35160493427) ^ 130708154 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35160493427) ^ 12969566 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35160493427) ^ 1458518 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_35593825229 : Nat.Prime 35593825229 := by
  apply lucas_primality 35593825229 (2 : ZMod 35593825229)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (277, 1), (2471107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (277, 1), (2471107, 1)] : List FactorBlock).map factorBlockValue).prod) = 35593825229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_277
      · exact prime_oneHundredFortyThreeEK_2471107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35593825229) ^ 17796912614 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35593825229) ^ 2737986556 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35593825229) ^ 128497564 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 35593825229) ^ 14404 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_38138276453 : Nat.Prime 38138276453 := by
  apply lucas_primality 38138276453 (2 : ZMod 38138276453)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (501819427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (501819427, 1)] : List FactorBlock).map factorBlockValue).prod) = 38138276453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_501819427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38138276453) ^ 19069138226 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38138276453) ^ 2007277708 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 38138276453) ^ 76 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_40475658263 : Nat.Prime 40475658263 := by
  apply lucas_primality 40475658263 (10 : ZMod 40475658263)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (223, 1), (6980969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (223, 1), (6980969, 1)] : List FactorBlock).map factorBlockValue).prod) = 40475658263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_223
      · exact prime_oneHundredFortyThreeEK_6980969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 40475658263) ^ 20237829131 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 40475658263) ^ 3113512174 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 40475658263) ^ 181505194 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 40475658263) ^ 5798 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_40715477573 : Nat.Prime 40715477573 := by
  apply lucas_primality 40715477573 (2 : ZMod 40715477573)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (132193109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (132193109, 1)] : List FactorBlock).map factorBlockValue).prod) = 40715477573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_132193109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40715477573) ^ 20357738786 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 40715477573) ^ 5816496796 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 40715477573) ^ 3701407052 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 40715477573) ^ 308 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_42466287607 : Nat.Prime 42466287607 := by
  apply lucas_primality 42466287607 (6 : ZMod 42466287607)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (416336153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (416336153, 1)] : List FactorBlock).map factorBlockValue).prod) = 42466287607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_416336153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 42466287607) ^ 21233143803 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 42466287607) ^ 14155429202 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 42466287607) ^ 2498016918 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 42466287607) ^ 102 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_47934499213 : Nat.Prime 47934499213 := by
  apply lucas_primality 47934499213 (2 : ZMod 47934499213)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7349, 1), (181183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7349, 1), (181183, 1)] : List FactorBlock).map factorBlockValue).prod) = 47934499213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7349
      · exact prime_oneHundredFortyThreeEK_181183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47934499213) ^ 23967249606 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 47934499213) ^ 15978166404 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 47934499213) ^ 6522588 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 47934499213) ^ 264564 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_55633490141 : Nat.Prime 55633490141 := by
  apply lucas_primality 55633490141 (2 : ZMod 55633490141)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (313, 1), (8887139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (313, 1), (8887139, 1)] : List FactorBlock).map factorBlockValue).prod) = 55633490141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_313
      · exact prime_oneHundredFortyThreeEK_8887139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55633490141) ^ 27816745070 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55633490141) ^ 11126698028 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55633490141) ^ 177742780 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 55633490141) ^ 6260 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_66920223787 : Nat.Prime 66920223787 := by
  apply lucas_primality 66920223787 (2 : ZMod 66920223787)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (983, 1), (872789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (983, 1), (872789, 1)] : List FactorBlock).map factorBlockValue).prod) = 66920223787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_983
      · exact prime_oneHundredFortyThreeEK_872789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66920223787) ^ 33460111893 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 66920223787) ^ 22306741262 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 66920223787) ^ 5147709522 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 66920223787) ^ 68077542 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 66920223787) ^ 76674 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_68800305961 : Nat.Prime 68800305961 := by
  apply lucas_primality 68800305961 (19 : ZMod 68800305961)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (167, 1), (381461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (167, 1), (381461, 1)] : List FactorBlock).map factorBlockValue).prod) = 68800305961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_167
      · exact prime_oneHundredFortyThreeEK_381461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 68800305961) ^ 34400152980 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (19 : ZMod 68800305961) ^ 22933435320 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (19 : ZMod 68800305961) ^ 13760061192 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (19 : ZMod 68800305961) ^ 411977880 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (19 : ZMod 68800305961) ^ 180360 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_70557964669 : Nat.Prime 70557964669 := by
  apply lucas_primality 70557964669 (6 : ZMod 70557964669)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1109, 1), (1767307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1109, 1), (1767307, 1)] : List FactorBlock).map factorBlockValue).prod) = 70557964669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_1109
      · exact prime_oneHundredFortyThreeEK_1767307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 70557964669) ^ 35278982334 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 70557964669) ^ 23519321556 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 70557964669) ^ 63623052 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 70557964669) ^ 39924 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_78408375347 : Nat.Prime 78408375347 := by
  apply lucas_primality 78408375347 (2 : ZMod 78408375347)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5600598239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5600598239, 1)] : List FactorBlock).map factorBlockValue).prod) = 78408375347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_5600598239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 78408375347) ^ 39204187673 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 78408375347) ^ 11201196478 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 78408375347) ^ 14 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_86435048143 : Nat.Prime 86435048143 := by
  apply lucas_primality 86435048143 (3 : ZMod 86435048143)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4801947119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4801947119, 1)] : List FactorBlock).map factorBlockValue).prod) = 86435048143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_4801947119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 86435048143) ^ 43217524071 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 86435048143) ^ 28811682714 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 86435048143) ^ 18 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_91255055459 : Nat.Prime 91255055459 := by
  apply lucas_primality 91255055459 (6 : ZMod 91255055459)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (163, 1), (251, 1), (159319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (163, 1), (251, 1), (159319, 1)] : List FactorBlock).map factorBlockValue).prod) = 91255055459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_163
      · exact prime_oneHundredFortyThreeEK_251
      · exact prime_oneHundredFortyThreeEK_159319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 91255055459) ^ 45627527729 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 91255055459) ^ 13036436494 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 91255055459) ^ 559846966 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 91255055459) ^ 363565958 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 91255055459) ^ 572782 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_106338405293 : Nat.Prime 106338405293 := by
  apply lucas_primality 106338405293 (3 : ZMod 106338405293)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (587, 1), (6469847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (587, 1), (6469847, 1)] : List FactorBlock).map factorBlockValue).prod) = 106338405293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_587
      · exact prime_oneHundredFortyThreeEK_6469847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 106338405293) ^ 53169202646 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 106338405293) ^ 15191200756 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 106338405293) ^ 181155716 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 106338405293) ^ 16436 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_118662433481 : Nat.Prime 118662433481 := by
  apply lucas_primality 118662433481 (6 : ZMod 118662433481)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) = 118662433481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_71
      · exact prime_oneHundredFortyThreeEK_79
      · exact prime_oneHundredFortyThreeEK_263
      · exact prime_oneHundredFortyThreeEK_2011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 118662433481) ^ 59331216740 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 23732486696 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1671301880 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1502056120 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 451187960 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 59006680 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_123457223749 : Nat.Prime 123457223749 := by
  apply lucas_primality 123457223749 (7 : ZMod 123457223749)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (127, 1), (835141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (127, 1), (835141, 1)] : List FactorBlock).map factorBlockValue).prod) = 123457223749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_97
      · exact prime_oneHundredFortyThreeEK_127
      · exact prime_oneHundredFortyThreeEK_835141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 123457223749) ^ 61728611874 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 123457223749) ^ 41152407916 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 123457223749) ^ 1272754884 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 123457223749) ^ 972104124 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 123457223749) ^ 147828 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_128133532651 : Nat.Prime 128133532651 := by
  apply lucas_primality 128133532651 (2 : ZMod 128133532651)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (37, 1), (23087123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (37, 1), (23087123, 1)] : List FactorBlock).map factorBlockValue).prod) = 128133532651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_37
      · exact prime_oneHundredFortyThreeEK_23087123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 128133532651) ^ 64066766325 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 128133532651) ^ 42711177550 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 128133532651) ^ 25626706530 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 128133532651) ^ 3463068450 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 128133532651) ^ 5550 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_137851866017 : Nat.Prime 137851866017 := by
  apply lucas_primality 137851866017 (3 : ZMod 137851866017)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (61, 1), (3070471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (61, 1), (3070471, 1)] : List FactorBlock).map factorBlockValue).prod) = 137851866017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_23
      · exact prime_oneHundredFortyThreeEK_61
      · exact prime_oneHundredFortyThreeEK_3070471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 137851866017) ^ 68925933008 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 137851866017) ^ 5993559392 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 137851866017) ^ 2259866656 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 137851866017) ^ 44896 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_142197159337 : Nat.Prime 142197159337 := by
  apply lucas_primality 142197159337 (5 : ZMod 142197159337)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5924881639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5924881639, 1)] : List FactorBlock).map factorBlockValue).prod) = 142197159337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5924881639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 142197159337) ^ 71098579668 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 142197159337) ^ 47399053112 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 142197159337) ^ 24 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_145920089531 : Nat.Prime 145920089531 := by
  apply lucas_primality 145920089531 (2 : ZMod 145920089531)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (347, 1), (42051899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (347, 1), (42051899, 1)] : List FactorBlock).map factorBlockValue).prod) = 145920089531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_347
      · exact prime_oneHundredFortyThreeEK_42051899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 145920089531) ^ 72960044765 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 145920089531) ^ 29184017906 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 145920089531) ^ 420518990 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 145920089531) ^ 3470 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_153169880527 : Nat.Prime 153169880527 := by
  apply lucas_primality 153169880527 (3 : ZMod 153169880527)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 2), (16783901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 2), (16783901, 1)] : List FactorBlock).map factorBlockValue).prod) = 153169880527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_16783901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 153169880527) ^ 76584940263 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 153169880527) ^ 51056626842 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 153169880527) ^ 11782298502 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 153169880527) ^ 9126 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_153988993507 : Nat.Prime 153988993507 := by
  apply lucas_primality 153988993507 (2 : ZMod 153988993507)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (523, 1), (5851, 1), (8387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (523, 1), (5851, 1), (8387, 1)] : List FactorBlock).map factorBlockValue).prod) = 153988993507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_523
      · exact prime_oneHundredFortyThreeEK_5851
      · exact prime_oneHundredFortyThreeEK_8387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 153988993507) ^ 76994496753 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 153988993507) ^ 51329664502 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 153988993507) ^ 294434022 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 153988993507) ^ 26318406 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 153988993507) ^ 18360438 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_201681184403 : Nat.Prime 201681184403 := by
  apply lucas_primality 201681184403 (2 : ZMod 201681184403)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (6761, 1), (210071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (6761, 1), (210071, 1)] : List FactorBlock).map factorBlockValue).prod) = 201681184403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_71
      · exact prime_oneHundredFortyThreeEK_6761
      · exact prime_oneHundredFortyThreeEK_210071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 201681184403) ^ 100840592201 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 201681184403) ^ 2840580062 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 201681184403) ^ 29830082 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 201681184403) ^ 960062 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_202927080359 : Nat.Prime 202927080359 := by
  apply lucas_primality 202927080359 (11 : ZMod 202927080359)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12959, 1), (7829581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12959, 1), (7829581, 1)] : List FactorBlock).map factorBlockValue).prod) = 202927080359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_12959
      · exact prime_oneHundredFortyThreeEK_7829581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 202927080359) ^ 101463540179 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 202927080359) ^ 15659162 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 202927080359) ^ 25918 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_255283445983 : Nat.Prime 255283445983 := by
  apply lucas_primality 255283445983 (6 : ZMod 255283445983)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (285551953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (285551953, 1)] : List FactorBlock).map factorBlockValue).prod) = 255283445983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_149
      · exact prime_oneHundredFortyThreeEK_285551953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 255283445983) ^ 127641722991 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 255283445983) ^ 85094481994 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 255283445983) ^ 1713311718 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 255283445983) ^ 894 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_293284993553 : Nat.Prime 293284993553 := by
  apply lucas_primality 293284993553 (3 : ZMod 293284993553)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3181, 1), (5762437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3181, 1), (5762437, 1)] : List FactorBlock).map factorBlockValue).prod) = 293284993553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3181
      · exact prime_oneHundredFortyThreeEK_5762437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 293284993553) ^ 146642496776 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 293284993553) ^ 92198992 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 293284993553) ^ 50896 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_325853860999 : Nat.Prime 325853860999 := by
  apply lucas_primality 325853860999 (3 : ZMod 325853860999)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359, 1), (2659, 1), (56893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359, 1), (2659, 1), (56893, 1)] : List FactorBlock).map factorBlockValue).prod) = 325853860999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_359
      · exact prime_oneHundredFortyThreeEK_2659
      · exact prime_oneHundredFortyThreeEK_56893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 325853860999) ^ 162926930499 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 325853860999) ^ 108617953666 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 325853860999) ^ 907670922 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 325853860999) ^ 122547522 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 325853860999) ^ 5727486 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_359589051383 : Nat.Prime 359589051383 := by
  apply lucas_primality 359589051383 (7 : ZMod 359589051383)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (8629, 1), (172199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (8629, 1), (172199, 1)] : List FactorBlock).map factorBlockValue).prod) = 359589051383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_8629
      · exact prime_oneHundredFortyThreeEK_172199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 359589051383) ^ 179794525691 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 359589051383) ^ 32689913762 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 359589051383) ^ 41672158 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 359589051383) ^ 2088218 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_379967397757 : Nat.Prime 379967397757 := by
  apply lucas_primality 379967397757 (2 : ZMod 379967397757)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (157, 1), (1013, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (157, 1), (1013, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod) = 379967397757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_89
      · exact prime_oneHundredFortyThreeEK_157
      · exact prime_oneHundredFortyThreeEK_1013
      · exact prime_oneHundredFortyThreeEK_2237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 379967397757) ^ 189983698878 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 379967397757) ^ 126655799252 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 379967397757) ^ 4269296604 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 379967397757) ^ 2420174508 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 379967397757) ^ 375091212 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 379967397757) ^ 169855788 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_454912320139 : Nat.Prime 454912320139 := by
  apply lucas_primality 454912320139 (7 : ZMod 454912320139)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3583, 1), (3797, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3583, 1), (3797, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) = 454912320139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_3583
      · exact prime_oneHundredFortyThreeEK_3797
      · exact prime_oneHundredFortyThreeEK_5573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 454912320139) ^ 227456160069 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 454912320139) ^ 151637440046 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 454912320139) ^ 126964086 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 454912320139) ^ 119808354 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 454912320139) ^ 81627906 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_476907466417 : Nat.Prime 476907466417 := by
  apply lucas_primality 476907466417 (10 : ZMod 476907466417)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) = 476907466417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_43
      · exact prime_oneHundredFortyThreeEK_73
      · exact prime_oneHundredFortyThreeEK_3165203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 476907466417) ^ 238453733208 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 158969155472 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 11090871312 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 6532978992 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 150672 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_481329911297 : Nat.Prime 481329911297 := by
  apply lucas_primality 481329911297 (3 : ZMod 481329911297)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (13, 2), (919, 1), (6053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (13, 2), (919, 1), (6053, 1)] : List FactorBlock).map factorBlockValue).prod) = 481329911297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_919
      · exact prime_oneHundredFortyThreeEK_6053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 481329911297) ^ 240664955648 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 481329911297) ^ 37025377792 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 481329911297) ^ 523753984 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 481329911297) ^ 79519232 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_488585730877 : Nat.Prime 488585730877 := by
  apply lucas_primality 488585730877 (5 : ZMod 488585730877)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (40715477573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (40715477573, 1)] : List FactorBlock).map factorBlockValue).prod) = 488585730877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_40715477573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 488585730877) ^ 244292865438 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 488585730877) ^ 162861910292 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 488585730877) ^ 12 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_577282082753 : Nat.Prime 577282082753 := by
  apply lucas_primality 577282082753 (3 : ZMod 577282082753)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (9020032543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (9020032543, 1)] : List FactorBlock).map factorBlockValue).prod) = 577282082753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_9020032543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 577282082753) ^ 288641041376 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 577282082753) ^ 64 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_603886289519 : Nat.Prime 603886289519 := by
  apply lucas_primality 603886289519 (7 : ZMod 603886289519)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (61, 1), (3373, 1), (77237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (61, 1), (3373, 1), (77237, 1)] : List FactorBlock).map factorBlockValue).prod) = 603886289519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_61
      · exact prime_oneHundredFortyThreeEK_3373
      · exact prime_oneHundredFortyThreeEK_77237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 603886289519) ^ 301943144759 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 603886289519) ^ 31783488922 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 603886289519) ^ 9899775238 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 603886289519) ^ 179035366 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 603886289519) ^ 7818614 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_608144872589 : Nat.Prime 608144872589 := by
  apply lucas_primality 608144872589 (2 : ZMod 608144872589)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (149, 1), (887, 1), (104579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (149, 1), (887, 1), (104579, 1)] : List FactorBlock).map factorBlockValue).prod) = 608144872589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_149
      · exact prime_oneHundredFortyThreeEK_887
      · exact prime_oneHundredFortyThreeEK_104579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 608144872589) ^ 304072436294 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 608144872589) ^ 55285897508 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 608144872589) ^ 4081509212 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 608144872589) ^ 685619924 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 608144872589) ^ 5815172 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_698664761017 : Nat.Prime 698664761017 := by
  apply lucas_primality 698664761017 (5 : ZMod 698664761017)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (939065539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (939065539, 1)] : List FactorBlock).map factorBlockValue).prod) = 698664761017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_939065539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 698664761017) ^ 349332380508 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 698664761017) ^ 232888253672 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 698664761017) ^ 22537572936 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 698664761017) ^ 744 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_736729429361 : Nat.Prime 736729429361 := by
  apply lucas_primality 736729429361 (3 : ZMod 736729429361)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (23, 1), (400396429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (23, 1), (400396429, 1)] : List FactorBlock).map factorBlockValue).prod) = 736729429361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_23
      · exact prime_oneHundredFortyThreeEK_400396429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 736729429361) ^ 368364714680 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 736729429361) ^ 147345885872 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 736729429361) ^ 32031714320 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 736729429361) ^ 1840 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1295508299753 : Nat.Prime 1295508299753 := by
  apply lucas_primality 1295508299753 (3 : ZMod 1295508299753)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1295508299753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_43759
      · exact prime_oneHundredFortyThreeEK_3700691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1295508299753) ^ 647754149876 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 29605528 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 350072 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1564506913061 : Nat.Prime 1564506913061 := by
  apply lucas_primality 1564506913061 (2 : ZMod 1564506913061)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1564506913061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_281
      · exact prime_oneHundredFortyThreeEK_3059143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1564506913061) ^ 782253456530 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 312901382612 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 223500987580 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 120346685620 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 5567640260 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 511420 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1845538883813 : Nat.Prime 1845538883813 := by
  apply lucas_primality 1845538883813 (2 : ZMod 1845538883813)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (4909, 1), (7229809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (4909, 1), (7229809, 1)] : List FactorBlock).map factorBlockValue).prod) = 1845538883813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_4909
      · exact prime_oneHundredFortyThreeEK_7229809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1845538883813) ^ 922769441906 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1845538883813) ^ 141964529524 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1845538883813) ^ 375950068 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1845538883813) ^ 255268 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2379366789509 : Nat.Prime 2379366789509 := by
  apply lucas_primality 2379366789509 (2 : ZMod 2379366789509)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (2447, 1), (2971, 1), (4813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (2447, 1), (2971, 1), (4813, 1)] : List FactorBlock).map factorBlockValue).prod) = 2379366789509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_2447
      · exact prime_oneHundredFortyThreeEK_2971
      · exact prime_oneHundredFortyThreeEK_4813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2379366789509) ^ 1189683394754 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2379366789509) ^ 139962752324 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2379366789509) ^ 972360764 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2379366789509) ^ 800863948 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2379366789509) ^ 494362516 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2676546708113 : Nat.Prime 2676546708113 := by
  apply lucas_primality 2676546708113 (3 : ZMod 2676546708113)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2676546708113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_107
      · exact prime_oneHundredFortyThreeEK_28729
      · exact prime_oneHundredFortyThreeEK_54419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2676546708113) ^ 1338273354056 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 25014455216 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 93165328 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 49184048 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_3629355878353 : Nat.Prime 3629355878353 := by
  apply lucas_primality 3629355878353 (5 : ZMod 3629355878353)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (2687, 1), (1655281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (2687, 1), (1655281, 1)] : List FactorBlock).map factorBlockValue).prod) = 3629355878353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_2687
      · exact prime_oneHundredFortyThreeEK_1655281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3629355878353) ^ 1814677939176 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3629355878353) ^ 1209785292784 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3629355878353) ^ 213491522256 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3629355878353) ^ 1350709296 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3629355878353) ^ 2192592 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_3848706415793 : Nat.Prime 3848706415793 := by
  apply lucas_primality 3848706415793 (5 : ZMod 3848706415793)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (19, 1), (1808602639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (19, 1), (1808602639, 1)] : List FactorBlock).map factorBlockValue).prod) = 3848706415793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_1808602639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3848706415793) ^ 1924353207896 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3848706415793) ^ 549815202256 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3848706415793) ^ 202563495568 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 3848706415793) ^ 2128 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_4580580428509 : Nat.Prime 4580580428509 := by
  apply lucas_primality 4580580428509 (6 : ZMod 4580580428509)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (74381, 1), (733127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (74381, 1), (733127, 1)] : List FactorBlock).map factorBlockValue).prod) = 4580580428509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_74381
      · exact prime_oneHundredFortyThreeEK_733127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4580580428509) ^ 2290290214254 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4580580428509) ^ 1526860142836 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4580580428509) ^ 654368632644 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4580580428509) ^ 61582668 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 4580580428509) ^ 6248004 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_5238370908647 : Nat.Prime 5238370908647 := by
  apply lucas_primality 5238370908647 (7 : ZMod 5238370908647)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (137851866017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (137851866017, 1)] : List FactorBlock).map factorBlockValue).prod) = 5238370908647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_137851866017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 5238370908647) ^ 2619185454323 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5238370908647) ^ 275703732034 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 5238370908647) ^ 38 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_5472872986837 : Nat.Prime 5472872986837 := by
  apply lucas_primality 5472872986837 (2 : ZMod 5472872986837)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (41, 1), (654336799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (41, 1), (654336799, 1)] : List FactorBlock).map factorBlockValue).prod) = 5472872986837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_41
      · exact prime_oneHundredFortyThreeEK_654336799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5472872986837) ^ 2736436493418 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5472872986837) ^ 1824290995612 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5472872986837) ^ 321933705108 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5472872986837) ^ 133484706996 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5472872986837) ^ 8364 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_9234964193801 : Nat.Prime 9234964193801 := by
  apply lucas_primality 9234964193801 (3 : ZMod 9234964193801)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7411, 1), (6230579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7411, 1), (6230579, 1)] : List FactorBlock).map factorBlockValue).prod) = 9234964193801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_7411
      · exact prime_oneHundredFortyThreeEK_6230579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9234964193801) ^ 4617482096900 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9234964193801) ^ 1846992838760 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9234964193801) ^ 1246115800 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 9234964193801) ^ 1482200 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_12215675149549 : Nat.Prime 12215675149549 := by
  apply lucas_primality 12215675149549 (2 : ZMod 12215675149549)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17, 1), (577, 1), (7983037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17, 1), (577, 1), (7983037, 1)] : List FactorBlock).map factorBlockValue).prod) = 12215675149549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_577
      · exact prime_oneHundredFortyThreeEK_7983037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12215675149549) ^ 6107837574774 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12215675149549) ^ 4071891716516 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12215675149549) ^ 939667319196 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12215675149549) ^ 718569126444 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12215675149549) ^ 21171014124 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12215675149549) ^ 1530204 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_12917076397133 : Nat.Prime 12917076397133 := by
  apply lucas_primality 12917076397133 (2 : ZMod 12917076397133)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (487, 1), (6630942709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (487, 1), (6630942709, 1)] : List FactorBlock).map factorBlockValue).prod) = 12917076397133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_487
      · exact prime_oneHundredFortyThreeEK_6630942709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12917076397133) ^ 6458538198566 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12917076397133) ^ 26523770836 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12917076397133) ^ 1948 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_12945205849789 : Nat.Prime 12945205849789 := by
  apply lucas_primality 12945205849789 (2 : ZMod 12945205849789)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (359589051383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (359589051383, 1)] : List FactorBlock).map factorBlockValue).prod) = 12945205849789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_359589051383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12945205849789) ^ 6472602924894 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12945205849789) ^ 4315068616596 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 12945205849789) ^ 36 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_15576951986611 : Nat.Prime 15576951986611 := by
  apply lucas_primality 15576951986611 (2 : ZMod 15576951986611)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (41, 1), (1279, 1), (83207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (41, 1), (1279, 1), (83207, 1)] : List FactorBlock).map factorBlockValue).prod) = 15576951986611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_41
      · exact prime_oneHundredFortyThreeEK_1279
      · exact prime_oneHundredFortyThreeEK_83207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15576951986611) ^ 7788475993305 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15576951986611) ^ 5192317328870 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15576951986611) ^ 3115390397322 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15576951986611) ^ 2225278855230 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15576951986611) ^ 916291293330 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15576951986611) ^ 379925658210 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15576951986611) ^ 12179008590 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 15576951986611) ^ 187207230 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_16611914849819 : Nat.Prime 16611914849819 := by
  apply lucas_primality 16611914849819 (2 : ZMod 16611914849819)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (488585730877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (488585730877, 1)] : List FactorBlock).map factorBlockValue).prod) = 16611914849819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_488585730877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16611914849819) ^ 8305957424909 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 16611914849819) ^ 977171461754 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 16611914849819) ^ 34 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_19019666571553 : Nat.Prime 19019666571553 := by
  apply lucas_primality 19019666571553 (10 : ZMod 19019666571553)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (20611, 1), (3204139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (20611, 1), (3204139, 1)] : List FactorBlock).map factorBlockValue).prod) = 19019666571553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_20611
      · exact prime_oneHundredFortyThreeEK_3204139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 19019666571553) ^ 9509833285776 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 19019666571553) ^ 6339888857184 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 19019666571553) ^ 922792032 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 19019666571553) ^ 5935968 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_21227934830437 : Nat.Prime 21227934830437 := by
  apply lucas_primality 21227934830437 (5 : ZMod 21227934830437)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (499, 1), (659, 1), (1793161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (499, 1), (659, 1), (1793161, 1)] : List FactorBlock).map factorBlockValue).prod) = 21227934830437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_499
      · exact prime_oneHundredFortyThreeEK_659
      · exact prime_oneHundredFortyThreeEK_1793161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21227934830437) ^ 10613967415218 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 21227934830437) ^ 7075978276812 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 21227934830437) ^ 42540951564 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 21227934830437) ^ 32212344204 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 21227934830437) ^ 11838276 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_23655440647229 : Nat.Prime 23655440647229 := by
  apply lucas_primality 23655440647229 (2 : ZMod 23655440647229)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (454912320139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (454912320139, 1)] : List FactorBlock).map factorBlockValue).prod) = 23655440647229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_454912320139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23655440647229) ^ 11827720323614 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 23655440647229) ^ 1819649280556 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 23655440647229) ^ 52 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_27447499024109 : Nat.Prime 27447499024109 := by
  apply lucas_primality 27447499024109 (2 : ZMod 27447499024109)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (18797, 1), (21473623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (18797, 1), (21473623, 1)] : List FactorBlock).map factorBlockValue).prod) = 27447499024109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_18797
      · exact prime_oneHundredFortyThreeEK_21473623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27447499024109) ^ 13723749512054 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27447499024109) ^ 1614558766124 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27447499024109) ^ 1460206364 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 27447499024109) ^ 1278196 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_31077730192021 : Nat.Prime 31077730192021 := by
  apply lucas_primality 31077730192021 (2 : ZMod 31077730192021)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1103, 1), (5413, 1), (86753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1103, 1), (5413, 1), (86753, 1)] : List FactorBlock).map factorBlockValue).prod) = 31077730192021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_1103
      · exact prime_oneHundredFortyThreeEK_5413
      · exact prime_oneHundredFortyThreeEK_86753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31077730192021) ^ 15538865096010 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31077730192021) ^ 10359243397340 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31077730192021) ^ 6215546038404 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31077730192021) ^ 28175639340 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31077730192021) ^ 5741313540 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31077730192021) ^ 358232340 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_31267537129187 : Nat.Prime 31267537129187 := by
  apply lucas_primality 31267537129187 (2 : ZMod 31267537129187)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (199457, 1), (78381649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (199457, 1), (78381649, 1)] : List FactorBlock).map factorBlockValue).prod) = 31267537129187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_199457
      · exact prime_oneHundredFortyThreeEK_78381649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31267537129187) ^ 15633768564593 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31267537129187) ^ 156763298 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 31267537129187) ^ 398914 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_33312673606897 : Nat.Prime 33312673606897 := by
  apply lucas_primality 33312673606897 (7 : ZMod 33312673606897)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) = 33312673606897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_151
      · exact prime_oneHundredFortyThreeEK_327289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 33312673606897) ^ 16656336803448 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 11104224535632 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 1074602374416 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 220613732496 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 101783664 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_43552270540237 : Nat.Prime 43552270540237 := by
  apply lucas_primality 43552270540237 (2 : ZMod 43552270540237)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3629355878353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3629355878353, 1)] : List FactorBlock).map factorBlockValue).prod) = 43552270540237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_3629355878353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43552270540237) ^ 21776135270118 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 43552270540237) ^ 14517423513412 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 43552270540237) ^ 12 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_54000412664701 : Nat.Prime 54000412664701 := by
  apply lucas_primality 54000412664701 (6 : ZMod 54000412664701)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (23, 1), (7826146763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (23, 1), (7826146763, 1)] : List FactorBlock).map factorBlockValue).prod) = 54000412664701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_23
      · exact prime_oneHundredFortyThreeEK_7826146763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 54000412664701) ^ 27000206332350 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 54000412664701) ^ 18000137554900 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 54000412664701) ^ 10800082532940 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 54000412664701) ^ 2347844028900 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 54000412664701) ^ 6900 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_65020302286831 : Nat.Prime 65020302286831 := by
  apply lucas_primality 65020302286831 (3 : ZMod 65020302286831)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (181, 1), (362856757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (181, 1), (362856757, 1)] : List FactorBlock).map factorBlockValue).prod) = 65020302286831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_181
      · exact prime_oneHundredFortyThreeEK_362856757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65020302286831) ^ 32510151143415 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 65020302286831) ^ 21673434095610 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 65020302286831) ^ 13004060457366 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 65020302286831) ^ 5910936571530 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 65020302286831) ^ 359228189430 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 65020302286831) ^ 179190 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_66139999399751 : Nat.Prime 66139999399751 := by
  apply lucas_primality 66139999399751 (7 : ZMod 66139999399751)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) = 66139999399751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_1321
      · exact prime_oneHundredFortyThreeEK_200272519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 66139999399751) ^ 33069999699875 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 13227999879950 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 50068129750 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 330250 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_74494291529123 : Nat.Prime 74494291529123 := by
  apply lucas_primality 74494291529123 (2 : ZMod 74494291529123)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (36293, 1), (35389313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (36293, 1), (35389313, 1)] : List FactorBlock).map factorBlockValue).prod) = 74494291529123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_29
      · exact prime_oneHundredFortyThreeEK_36293
      · exact prime_oneHundredFortyThreeEK_35389313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74494291529123) ^ 37247145764561 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 74494291529123) ^ 2568768673418 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 74494291529123) ^ 2052580154 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 74494291529123) ^ 2104994 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_115342509540833 : Nat.Prime 115342509540833 := by
  apply lucas_primality 115342509540833 (3 : ZMod 115342509540833)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) = 115342509540833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_2777
      · exact prime_oneHundredFortyThreeEK_185423809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 115342509540833) ^ 57671254770416 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 16477501362976 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 41534933216 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 622048 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_203545667016883 : Nat.Prime 203545667016883 := by
  apply lucas_primality 203545667016883 (2 : ZMod 203545667016883)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1128557, 1), (10019957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1128557, 1), (10019957, 1)] : List FactorBlock).map factorBlockValue).prod) = 203545667016883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_1128557
      · exact prime_oneHundredFortyThreeEK_10019957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 203545667016883) ^ 101772833508441 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 203545667016883) ^ 67848555672294 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 203545667016883) ^ 180359226 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 203545667016883) ^ 20314026 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_248177012270051 : Nat.Prime 248177012270051 := by
  apply lucas_primality 248177012270051 (2 : ZMod 248177012270051)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1096763, 1), (4525627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1096763, 1), (4525627, 1)] : List FactorBlock).map factorBlockValue).prod) = 248177012270051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_1096763
      · exact prime_oneHundredFortyThreeEK_4525627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 248177012270051) ^ 124088506135025 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 248177012270051) ^ 49635402454010 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 248177012270051) ^ 226281350 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 248177012270051) ^ 54838150 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_253822359934141 : Nat.Prime 253822359934141 := by
  apply lucas_primality 253822359934141 (6 : ZMod 253822359934141)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (479, 1), (8831675711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (479, 1), (8831675711, 1)] : List FactorBlock).map factorBlockValue).prod) = 253822359934141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_479
      · exact prime_oneHundredFortyThreeEK_8831675711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 253822359934141) ^ 126911179967070 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 253822359934141) ^ 84607453311380 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 253822359934141) ^ 50764471986828 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 253822359934141) ^ 529900542660 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 253822359934141) ^ 28740 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_267494201311979 : Nat.Prime 267494201311979 := by
  apply lucas_primality 267494201311979 (6 : ZMod 267494201311979)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) = 267494201311979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_97
      · exact prime_oneHundredFortyThreeEK_107
      · exact prime_oneHundredFortyThreeEK_12886318591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 267494201311979) ^ 133747100655989 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2757672178474 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2499945806654 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 20758 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_319596396058409 : Nat.Prime 319596396058409 := by
  apply lucas_primality 319596396058409 (3 : ZMod 319596396058409)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1783, 1), (3200829221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1783, 1), (3200829221, 1)] : List FactorBlock).map factorBlockValue).prod) = 319596396058409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_1783
      · exact prime_oneHundredFortyThreeEK_3200829221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 319596396058409) ^ 159798198029204 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 319596396058409) ^ 45656628008344 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 319596396058409) ^ 179246436376 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 319596396058409) ^ 99848 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_340027810279433 : Nat.Prime 340027810279433 := by
  apply lucas_primality 340027810279433 (3 : ZMod 340027810279433)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (31, 1), (79, 1), (143433401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (31, 1), (79, 1), (143433401, 1)] : List FactorBlock).map factorBlockValue).prod) = 340027810279433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_79
      · exact prime_oneHundredFortyThreeEK_143433401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 340027810279433) ^ 170013905139716 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 340027810279433) ^ 30911619116312 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 340027810279433) ^ 10968639041272 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 340027810279433) ^ 4304149497208 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 340027810279433) ^ 2370632 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_404854780352999 : Nat.Prime 404854780352999 := by
  apply lucas_primality 404854780352999 (7 : ZMod 404854780352999)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (103, 1), (47934499213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (103, 1), (47934499213, 1)] : List FactorBlock).map factorBlockValue).prod) = 404854780352999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_41
      · exact prime_oneHundredFortyThreeEK_103
      · exact prime_oneHundredFortyThreeEK_47934499213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 404854780352999) ^ 202427390176499 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 404854780352999) ^ 9874506837878 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 404854780352999) ^ 3930628935466 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 404854780352999) ^ 8446 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_684349746850837 : Nat.Prime 684349746850837 := by
  apply lucas_primality 684349746850837 (2 : ZMod 684349746850837)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (89, 1), (19417482319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (89, 1), (19417482319, 1)] : List FactorBlock).map factorBlockValue).prod) = 684349746850837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_89
      · exact prime_oneHundredFortyThreeEK_19417482319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 684349746850837) ^ 342174873425418 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 684349746850837) ^ 228116582283612 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 684349746850837) ^ 62213613350076 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 684349746850837) ^ 7689322998324 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 684349746850837) ^ 35244 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_696203753478533 : Nat.Prime 696203753478533 := by
  apply lucas_primality 696203753478533 (2 : ZMod 696203753478533)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (73, 1), (293, 1), (625954169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (73, 1), (293, 1), (625954169, 1)] : List FactorBlock).map factorBlockValue).prod) = 696203753478533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_73
      · exact prime_oneHundredFortyThreeEK_293
      · exact prime_oneHundredFortyThreeEK_625954169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 696203753478533) ^ 348101876739266 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 696203753478533) ^ 53554134882964 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 696203753478533) ^ 9537037718884 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 696203753478533) ^ 2376122025524 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 696203753478533) ^ 1112228 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_810117218002061 : Nat.Prime 810117218002061 := by
  apply lucas_primality 810117218002061 (2 : ZMod 810117218002061)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (79, 1), (22292713759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (79, 1), (22292713759, 1)] : List FactorBlock).map factorBlockValue).prod) = 810117218002061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_23
      · exact prime_oneHundredFortyThreeEK_79
      · exact prime_oneHundredFortyThreeEK_22292713759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 810117218002061) ^ 405058609001030 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 162023443600412 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 35222487739220 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 10254648329140 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 810117218002061) ^ 36340 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_889454707390463 : Nat.Prime 889454707390463 := by
  apply lucas_primality 889454707390463 (5 : ZMod 889454707390463)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (74189, 1), (5994518779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (74189, 1), (5994518779, 1)] : List FactorBlock).map factorBlockValue).prod) = 889454707390463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_74189
      · exact prime_oneHundredFortyThreeEK_5994518779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 889454707390463) ^ 444727353695231 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 889454707390463) ^ 11989037558 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 889454707390463) ^ 148378 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1455150267657277 : Nat.Prime 1455150267657277 := by
  apply lucas_primality 1455150267657277 (5 : ZMod 1455150267657277)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (71, 1), (2927, 1), (12415027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (71, 1), (2927, 1), (12415027, 1)] : List FactorBlock).map factorBlockValue).prod) = 1455150267657277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_47
      · exact prime_oneHundredFortyThreeEK_71
      · exact prime_oneHundredFortyThreeEK_2927
      · exact prime_oneHundredFortyThreeEK_12415027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1455150267657277) ^ 727575133828638 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1455150267657277) ^ 485050089219092 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1455150267657277) ^ 30960643992708 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1455150267657277) ^ 20495074192356 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1455150267657277) ^ 497147341188 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1455150267657277) ^ 117208788 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1461186156123301 : Nat.Prime 1461186156123301 := by
  apply lucas_primality 1461186156123301 (2 : ZMod 1461186156123301)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (31, 1), (79, 1), (283, 1), (7027633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (31, 1), (79, 1), (283, 1), (7027633, 1)] : List FactorBlock).map factorBlockValue).prod) = 1461186156123301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_79
      · exact prime_oneHundredFortyThreeEK_283
      · exact prime_oneHundredFortyThreeEK_7027633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1461186156123301) ^ 730593078061650 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461186156123301) ^ 487062052041100 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461186156123301) ^ 292237231224660 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461186156123301) ^ 47135037294300 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461186156123301) ^ 18496027292700 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461186156123301) ^ 5163201965100 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1461186156123301) ^ 207920100 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1881330558075919 : Nat.Prime 1881330558075919 := by
  apply lucas_primality 1881330558075919 (3 : ZMod 1881330558075919)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (43, 1), (78408375347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (43, 1), (78408375347, 1)] : List FactorBlock).map factorBlockValue).prod) = 1881330558075919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_43
      · exact prime_oneHundredFortyThreeEK_78408375347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1881330558075919) ^ 940665279037959 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1881330558075919) ^ 627110186025306 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1881330558075919) ^ 60688082518578 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1881330558075919) ^ 43751873443626 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1881330558075919) ^ 23994 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2229338079331339 : Nat.Prime 2229338079331339 := by
  apply lucas_primality 2229338079331339 (3 : ZMod 2229338079331339)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (19, 1), (191, 1), (359, 1), (986837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (19, 1), (191, 1), (359, 1), (986837, 1)] : List FactorBlock).map factorBlockValue).prod) = 2229338079331339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_191
      · exact prime_oneHundredFortyThreeEK_359
      · exact prime_oneHundredFortyThreeEK_986837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2229338079331339) ^ 1114669039665669 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2229338079331339) ^ 743112693110446 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2229338079331339) ^ 131137534078314 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2229338079331339) ^ 117333583122702 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2229338079331339) ^ 11671927116918 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2229338079331339) ^ 6209855374182 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2229338079331339) ^ 2259074274 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_3877729964228453 : Nat.Prime 3877729964228453 := by
  apply lucas_primality 3877729964228453 (2 : ZMod 3877729964228453)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (557, 1), (40475658263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (557, 1), (40475658263, 1)] : List FactorBlock).map factorBlockValue).prod) = 3877729964228453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_43
      · exact prime_oneHundredFortyThreeEK_557
      · exact prime_oneHundredFortyThreeEK_40475658263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3877729964228453) ^ 1938864982114226 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3877729964228453) ^ 90179766609964 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3877729964228453) ^ 6961813221236 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3877729964228453) ^ 95804 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_6091573588046347 : Nat.Prime 6091573588046347 := by
  apply lucas_primality 6091573588046347 (2 : ZMod 6091573588046347)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (97, 1), (255283445983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (97, 1), (255283445983, 1)] : List FactorBlock).map factorBlockValue).prod) = 6091573588046347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_41
      · exact prime_oneHundredFortyThreeEK_97
      · exact prime_oneHundredFortyThreeEK_255283445983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6091573588046347) ^ 3045786794023173 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6091573588046347) ^ 2030524529348782 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6091573588046347) ^ 148574965562106 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6091573588046347) ^ 62799727711818 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6091573588046347) ^ 23862 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_6982819718723939 : Nat.Prime 6982819718723939 := by
  apply lucas_primality 6982819718723939 (2 : ZMod 6982819718723939)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6982819718723939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_79
      · exact prime_oneHundredFortyThreeEK_1583
      · exact prime_oneHundredFortyThreeEK_27918548017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6982819718723939) ^ 3491409859361969 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 88390123021822 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 4411130586686 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 250114 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_8560070626452379 : Nat.Prime 8560070626452379 := by
  apply lucas_primality 8560070626452379 (2 : ZMod 8560070626452379)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) = 8560070626452379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_1093
      · exact prime_oneHundredFortyThreeEK_118662433481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8560070626452379) ^ 4280035313226189 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 2853356875484126 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 778188238768398 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 7831720609746 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 72138 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_8917352317325357 : Nat.Prime 8917352317325357 := by
  apply lucas_primality 8917352317325357 (2 : ZMod 8917352317325357)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2229338079331339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2229338079331339, 1)] : List FactorBlock).map factorBlockValue).prod) = 8917352317325357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_2229338079331339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 8917352317325357) ^ 4458676158662678 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 8917352317325357) ^ 4 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_13514938644715877 : Nat.Prime 13514938644715877 := by
  apply lucas_primality 13514938644715877 (2 : ZMod 13514938644715877)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (37, 1), (1223, 1), (60077, 1), (65413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (37, 1), (1223, 1), (60077, 1), (65413, 1)] : List FactorBlock).map factorBlockValue).prod) = 13514938644715877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_37
      · exact prime_oneHundredFortyThreeEK_1223
      · exact prime_oneHundredFortyThreeEK_60077
      · exact prime_oneHundredFortyThreeEK_65413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13514938644715877) ^ 6757469322357938 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13514938644715877) ^ 711312560248204 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13514938644715877) ^ 365268612019348 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13514938644715877) ^ 11050644844412 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13514938644715877) ^ 224960278388 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 13514938644715877) ^ 206609368852 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_19798144074862999 : Nat.Prime 19798144074862999 := by
  apply lucas_primality 19798144074862999 (12 : ZMod 19798144074862999)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (253822359934141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (253822359934141, 1)] : List FactorBlock).map factorBlockValue).prod) = 19798144074862999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_253822359934141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 19798144074862999) ^ 9899072037431499 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (12 : ZMod 19798144074862999) ^ 6599381358287666 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (12 : ZMod 19798144074862999) ^ 1522934159604846 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (12 : ZMod 19798144074862999) ^ 78 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_41232416128919203 : Nat.Prime 41232416128919203 := by
  apply lucas_primality 41232416128919203 (3 : ZMod 41232416128919203)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 2), (11423, 1), (151498199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 2), (11423, 1), (151498199, 1)] : List FactorBlock).map factorBlockValue).prod) = 41232416128919203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_11423
      · exact prime_oneHundredFortyThreeEK_151498199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41232416128919203) ^ 20616208064459601 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41232416128919203) ^ 13744138709639734 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41232416128919203) ^ 3748401466265382 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41232416128919203) ^ 2170127164679958 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41232416128919203) ^ 3609596089374 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 41232416128919203) ^ 272164398 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_44269697545948463 : Nat.Prime 44269697545948463 := by
  apply lucas_primality 44269697545948463 (5 : ZMod 44269697545948463)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (29, 1), (15576951986611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (29, 1), (15576951986611, 1)] : List FactorBlock).map factorBlockValue).prod) = 44269697545948463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_29
      · exact prime_oneHundredFortyThreeEK_15576951986611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 44269697545948463) ^ 22134848772974231 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 44269697545948463) ^ 6324242506564066 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 44269697545948463) ^ 1526541294687878 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 44269697545948463) ^ 2842 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_46367973446495333 : Nat.Prime 46367973446495333 := by
  apply lucas_primality 46367973446495333 (2 : ZMod 46367973446495333)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (373, 1), (31077730192021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (373, 1), (31077730192021, 1)] : List FactorBlock).map factorBlockValue).prod) = 46367973446495333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_373
      · exact prime_oneHundredFortyThreeEK_31077730192021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46367973446495333) ^ 23183986723247666 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46367973446495333) ^ 124310920768084 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 46367973446495333) ^ 1492 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_62601469449873373 : Nat.Prime 62601469449873373 := by
  apply lucas_primality 62601469449873373 (2 : ZMod 62601469449873373)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (701, 1), (145920089531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (701, 1), (145920089531, 1)] : List FactorBlock).map factorBlockValue).prod) = 62601469449873373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_701
      · exact prime_oneHundredFortyThreeEK_145920089531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62601469449873373) ^ 31300734724936686 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 62601469449873373) ^ 20867156483291124 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 62601469449873373) ^ 3682439379404316 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 62601469449873373) ^ 89303094792972 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 62601469449873373) ^ 429012 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_78511797954027271 : Nat.Prime 78511797954027271 := by
  apply lucas_primality 78511797954027271 (3 : ZMod 78511797954027271)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) = 78511797954027271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_3457
      · exact prime_oneHundredFortyThreeEK_8263
      · exact prime_oneHundredFortyThreeEK_4362719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78511797954027271) ^ 39255898977013635 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 26170599318009090 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 15702359590805454 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 11215971136289610 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 22710962671110 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 9501609337290 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 17996070330 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_97839167941298939 : Nat.Prime 97839167941298939 := by
  apply lucas_primality 97839167941298939 (2 : ZMod 97839167941298939)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (3463, 1), (348307, 1), (526717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (3463, 1), (348307, 1), (526717, 1)] : List FactorBlock).map factorBlockValue).prod) = 97839167941298939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_3463
      · exact prime_oneHundredFortyThreeEK_348307
      · exact prime_oneHundredFortyThreeEK_526717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 97839167941298939) ^ 48919583970649469 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97839167941298939) ^ 13977023991614134 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97839167941298939) ^ 8894469812845358 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97839167941298939) ^ 28252719590326 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97839167941298939) ^ 280899229534 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 97839167941298939) ^ 185752819714 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_128584381738850489 : Nat.Prime 128584381738850489 := by
  apply lucas_primality 128584381738850489 (3 : ZMod 128584381738850489)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (1461186156123301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (1461186156123301, 1)] : List FactorBlock).map factorBlockValue).prod) = 128584381738850489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_1461186156123301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 128584381738850489) ^ 64292190869425244 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 128584381738850489) ^ 11689489248986408 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 128584381738850489) ^ 88 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_177112743868002511 : Nat.Prime 177112743868002511 := by
  apply lucas_primality 177112743868002511 (6 : ZMod 177112743868002511)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) = 177112743868002511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_281
      · exact prime_oneHundredFortyThreeEK_678593
      · exact prime_oneHundredFortyThreeEK_10320283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 177112743868002511) ^ 88556371934001255 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 59037581289334170 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 35422548773600502 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 630294462163710 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 260999957070 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 17161616970 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_257168763477700979 : Nat.Prime 257168763477700979 := by
  apply lucas_primality 257168763477700979 (2 : ZMod 257168763477700979)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (128584381738850489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (128584381738850489, 1)] : List FactorBlock).map factorBlockValue).prod) = 257168763477700979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_128584381738850489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 257168763477700979) ^ 128584381738850489 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 257168763477700979) ^ 2 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_273483609494575657 : Nat.Prime 273483609494575657 := by
  apply lucas_primality 273483609494575657 (5 : ZMod 273483609494575657)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (47, 1), (57899, 1), (380678593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (47, 1), (57899, 1), (380678593, 1)] : List FactorBlock).map factorBlockValue).prod) = 273483609494575657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_47
      · exact prime_oneHundredFortyThreeEK_57899
      · exact prime_oneHundredFortyThreeEK_380678593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 273483609494575657) ^ 136741804747287828 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 273483609494575657) ^ 91161203164858552 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 273483609494575657) ^ 24862146317688696 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 273483609494575657) ^ 5818800202012248 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 273483609494575657) ^ 4723459981944 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 273483609494575657) ^ 718410792 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_514127433193233229 : Nat.Prime 514127433193233229 := by
  apply lucas_primality 514127433193233229 (2 : ZMod 514127433193233229)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (73, 1), (54367, 1), (1199468351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (73, 1), (54367, 1), (1199468351, 1)] : List FactorBlock).map factorBlockValue).prod) = 514127433193233229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_73
      · exact prime_oneHundredFortyThreeEK_54367
      · exact prime_oneHundredFortyThreeEK_1199468351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 514127433193233229) ^ 257063716596616614 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 514127433193233229) ^ 171375811064411076 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 514127433193233229) ^ 7042841550592236 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 514127433193233229) ^ 9456608479284 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 514127433193233229) ^ 428629428 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_558033346683926017 : Nat.Prime 558033346683926017 := by
  apply lucas_primality 558033346683926017 (13 : ZMod 558033346683926017)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (19, 1), (271, 1), (70557964669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (19, 1), (271, 1), (70557964669, 1)] : List FactorBlock).map factorBlockValue).prod) = 558033346683926017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_271
      · exact prime_oneHundredFortyThreeEK_70557964669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 558033346683926017) ^ 279016673341963008 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (13 : ZMod 558033346683926017) ^ 186011115561308672 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (13 : ZMod 558033346683926017) ^ 29370176141259264 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (13 : ZMod 558033346683926017) ^ 2059163640900096 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (13 : ZMod 558033346683926017) ^ 7908864 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_568527232526486017 : Nat.Prime 568527232526486017 := by
  apply lucas_primality 568527232526486017 (5 : ZMod 568527232526486017)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (7, 3), (2789, 1), (386916653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (7, 3), (2789, 1), (386916653, 1)] : List FactorBlock).map factorBlockValue).prod) = 568527232526486017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_2789
      · exact prime_oneHundredFortyThreeEK_386916653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 568527232526486017) ^ 284263616263243008 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 568527232526486017) ^ 189509077508828672 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 568527232526486017) ^ 81218176075212288 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 568527232526486017) ^ 203846264799744 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 568527232526486017) ^ 1469379072 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_861161495993700833 : Nat.Prime 861161495993700833 := by
  apply lucas_primality 861161495993700833 (3 : ZMod 861161495993700833)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (109, 1), (1265639, 1), (27867643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (109, 1), (1265639, 1), (27867643, 1)] : List FactorBlock).map factorBlockValue).prod) = 861161495993700833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_109
      · exact prime_oneHundredFortyThreeEK_1265639
      · exact prime_oneHundredFortyThreeEK_27867643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 861161495993700833) ^ 430580747996850416 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 861161495993700833) ^ 123023070856242976 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 861161495993700833) ^ 7900564183428448 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 861161495993700833) ^ 680416371488 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 861161495993700833) ^ 30901841824 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1015278271831597447 : Nat.Prime 1015278271831597447 := by
  apply lucas_primality 1015278271831597447 (3 : ZMod 1015278271831597447)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (819827, 1), (68800305961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (819827, 1), (68800305961, 1)] : List FactorBlock).map factorBlockValue).prod) = 1015278271831597447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_819827
      · exact prime_oneHundredFortyThreeEK_68800305961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1015278271831597447) ^ 507639135915798723 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1015278271831597447) ^ 338426090610532482 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1015278271831597447) ^ 1238405507298 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1015278271831597447) ^ 14756886 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1109188763774599357 : Nat.Prime 1109188763774599357 := by
  apply lucas_primality 1109188763774599357 (5 : ZMod 1109188763774599357)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (89, 1), (199, 1), (29485457179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (89, 1), (199, 1), (29485457179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1109188763774599357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_59
      · exact prime_oneHundredFortyThreeEK_89
      · exact prime_oneHundredFortyThreeEK_199
      · exact prime_oneHundredFortyThreeEK_29485457179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1109188763774599357) ^ 554594381887299678 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 369729587924866452 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 18799809555501684 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 12462795098591004 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 5573812883289444 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 37618164 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1289175892739461933 : Nat.Prime 1289175892739461933 := by
  apply lucas_primality 1289175892739461933 (6 : ZMod 1289175892739461933)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8317, 1), (12917076397133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8317, 1), (12917076397133, 1)] : List FactorBlock).map factorBlockValue).prod) = 1289175892739461933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_8317
      · exact prime_oneHundredFortyThreeEK_12917076397133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1289175892739461933) ^ 644587946369730966 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1289175892739461933) ^ 429725297579820644 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1289175892739461933) ^ 155004916765596 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 1289175892739461933) ^ 99804 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1369414921968654929 : Nat.Prime 1369414921968654929 := by
  apply lucas_primality 1369414921968654929 (3 : ZMod 1369414921968654929)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (131, 1), (463, 1), (38138276453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (131, 1), (463, 1), (38138276453, 1)] : List FactorBlock).map factorBlockValue).prod) = 1369414921968654929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_37
      · exact prime_oneHundredFortyThreeEK_131
      · exact prime_oneHundredFortyThreeEK_463
      · exact prime_oneHundredFortyThreeEK_38138276453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1369414921968654929) ^ 684707460984327464 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1369414921968654929) ^ 37011214107260944 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1369414921968654929) ^ 10453549022661488 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1369414921968654929) ^ 2957699615483056 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1369414921968654929) ^ 35906576 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2139799712767801801 : Nat.Prime 2139799712767801801 := by
  apply lucas_primality 2139799712767801801 (7 : ZMod 2139799712767801801)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (49261, 1), (129347, 1), (559709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (49261, 1), (129347, 1), (559709, 1)] : List FactorBlock).map factorBlockValue).prod) = 2139799712767801801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_49261
      · exact prime_oneHundredFortyThreeEK_129347
      · exact prime_oneHundredFortyThreeEK_559709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2139799712767801801) ^ 1069899856383900900 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2139799712767801801) ^ 713266570922600600 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2139799712767801801) ^ 427959942553560360 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2139799712767801801) ^ 43438008013800 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2139799712767801801) ^ 16543095029400 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 2139799712767801801) ^ 3823057540200 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2871575644592147027 : Nat.Prime 2871575644592147027 := by
  apply lucas_primality 2871575644592147027 (2 : ZMod 2871575644592147027)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (15501823, 1), (4026981697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (15501823, 1), (4026981697, 1)] : List FactorBlock).map factorBlockValue).prod) = 2871575644592147027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_23
      · exact prime_oneHundredFortyThreeEK_15501823
      · exact prime_oneHundredFortyThreeEK_4026981697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2871575644592147027) ^ 1435787822296073513 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871575644592147027) ^ 124851114982267262 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871575644592147027) ^ 185241158062 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2871575644592147027) ^ 713083858 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2927544154246713619 : Nat.Prime 2927544154246713619 := by
  apply lucas_primality 2927544154246713619 (3 : ZMod 2927544154246713619)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) = 2927544154246713619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_8560070626452379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2927544154246713619) ^ 1463772077123356809 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 975848051415571206 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 154081271276142822 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 342 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_3014995691311940443 : Nat.Prime 3014995691311940443 := by
  apply lucas_primality 3014995691311940443 (2 : ZMod 3014995691311940443)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) = 3014995691311940443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_321187
      · exact prime_oneHundredFortyThreeEK_1564506913061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3014995691311940443) ^ 1507497845655970221 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1004998563770646814 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 9387041478366 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1927122 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_3038891933585684531 : Nat.Prime 3038891933585684531 := by
  apply lucas_primality 3038891933585684531 (2 : ZMod 3038891933585684531)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (9719, 1), (31267537129187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (9719, 1), (31267537129187, 1)] : List FactorBlock).map factorBlockValue).prod) = 3038891933585684531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_9719
      · exact prime_oneHundredFortyThreeEK_31267537129187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3038891933585684531) ^ 1519445966792842265 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3038891933585684531) ^ 607778386717136906 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3038891933585684531) ^ 312675371291870 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 3038891933585684531) ^ 97190 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_5061602178826836037 : Nat.Prime 5061602178826836037 := by
  apply lucas_primality 5061602178826836037 (2 : ZMod 5061602178826836037)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (31, 1), (739, 1), (855947, 1), (1265333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (31, 1), (739, 1), (855947, 1), (1265333, 1)] : List FactorBlock).map factorBlockValue).prod) = 5061602178826836037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_739
      · exact prime_oneHundredFortyThreeEK_855947
      · exact prime_oneHundredFortyThreeEK_1265333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5061602178826836037) ^ 2530801089413418018 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5061602178826836037) ^ 1687200726275612012 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5061602178826836037) ^ 297741304636872708 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5061602178826836037) ^ 163277489639575356 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5061602178826836037) ^ 6849258699359724 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5061602178826836037) ^ 5913452794188 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 5061602178826836037) ^ 4000213523892 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_12444465918338666353 : Nat.Prime 12444465918338666353 := by
  apply lucas_primality 12444465918338666353 (10 : ZMod 12444465918338666353)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (646937, 1), (19083311537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (646937, 1), (19083311537, 1)] : List FactorBlock).map factorBlockValue).prod) = 12444465918338666353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_646937
      · exact prime_oneHundredFortyThreeEK_19083311537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 12444465918338666353) ^ 6222232959169333176 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 12444465918338666353) ^ 4148155306112888784 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 12444465918338666353) ^ 1777780845476952336 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 12444465918338666353) ^ 19235978029296 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 12444465918338666353) ^ 652112496 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_14482091339026052653 : Nat.Prime 14482091339026052653 := by
  apply lucas_primality 14482091339026052653 (2 : ZMod 14482091339026052653)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (31, 1), (2833, 1), (4580580428509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (31, 1), (2833, 1), (4580580428509, 1)] : List FactorBlock).map factorBlockValue).prod) = 14482091339026052653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_2833
      · exact prime_oneHundredFortyThreeEK_4580580428509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14482091339026052653) ^ 7241045669513026326 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 14482091339026052653) ^ 4827363779675350884 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 14482091339026052653) ^ 467164236742775892 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 14482091339026052653) ^ 5111927758216044 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 14482091339026052653) ^ 3161628 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_15889643348031486049 : Nat.Prime 15889643348031486049 := by
  apply lucas_primality 15889643348031486049 (17 : ZMod 15889643348031486049)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (6997, 1), (23655440647229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (6997, 1), (23655440647229, 1)] : List FactorBlock).map factorBlockValue).prod) = 15889643348031486049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_6997
      · exact prime_oneHundredFortyThreeEK_23655440647229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 15889643348031486049) ^ 7944821674015743024 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (17 : ZMod 15889643348031486049) ^ 5296547782677162016 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (17 : ZMod 15889643348031486049) ^ 2270922302133984 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (17 : ZMod 15889643348031486049) ^ 671712 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_16396916337010523729 : Nat.Prime 16396916337010523729 := by
  apply lucas_primality 16396916337010523729 (3 : ZMod 16396916337010523729)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37337, 1), (27447499024109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37337, 1), (27447499024109, 1)] : List FactorBlock).map factorBlockValue).prod) = 16396916337010523729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_37337
      · exact prime_oneHundredFortyThreeEK_27447499024109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16396916337010523729) ^ 8198458168505261864 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 16396916337010523729) ^ 439159984385744 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 16396916337010523729) ^ 597392 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_24393322929934562299 : Nat.Prime 24393322929934562299 := by
  apply lucas_primality 24393322929934562299 (2 : ZMod 24393322929934562299)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (175727, 1), (325853860999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (175727, 1), (325853860999, 1)] : List FactorBlock).map factorBlockValue).prod) = 24393322929934562299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_71
      · exact prime_oneHundredFortyThreeEK_175727
      · exact prime_oneHundredFortyThreeEK_325853860999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24393322929934562299) ^ 12196661464967281149 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24393322929934562299) ^ 8131107643311520766 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24393322929934562299) ^ 343567928590627638 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24393322929934562299) ^ 138813744785574 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 24393322929934562299) ^ 74859702 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_26956897165701837953 : Nat.Prime 26956897165701837953 := by
  apply lucas_primality 26956897165701837953 (5 : ZMod 26956897165701837953)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (41, 1), (79, 1), (65020302286831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (41, 1), (79, 1), (65020302286831, 1)] : List FactorBlock).map factorBlockValue).prod) = 26956897165701837953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_41
      · exact prime_oneHundredFortyThreeEK_79
      · exact prime_oneHundredFortyThreeEK_65020302286831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 26956897165701837953) ^ 13478448582850918976 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26956897165701837953) ^ 657485296724435072 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26956897165701837953) ^ 341226546401289088 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 26956897165701837953) ^ 414592 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_38157275497106586211 : Nat.Prime 38157275497106586211 := by
  apply lucas_primality 38157275497106586211 (3 : ZMod 38157275497106586211)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (97839167941298939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (97839167941298939, 1)] : List FactorBlock).map factorBlockValue).prod) = 38157275497106586211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_97839167941298939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38157275497106586211) ^ 19078637748553293105 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 38157275497106586211) ^ 12719091832368862070 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 38157275497106586211) ^ 7631455099421317242 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 38157275497106586211) ^ 2935175038238968170 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 38157275497106586211) ^ 390 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_67912571720353889203 : Nat.Prime 67912571720353889203 := by
  apply lucas_primality 67912571720353889203 (11 : ZMod 67912571720353889203)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (130951069, 1), (86435048143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (130951069, 1), (86435048143, 1)] : List FactorBlock).map factorBlockValue).prod) = 67912571720353889203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_130951069
      · exact prime_oneHundredFortyThreeEK_86435048143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 67912571720353889203) ^ 33956285860176944601 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 67912571720353889203) ^ 22637523906784629734 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 67912571720353889203) ^ 518610288858 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 67912571720353889203) ^ 785706414 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_68103288955401349211 : Nat.Prime 68103288955401349211 := by
  apply lucas_primality 68103288955401349211 (2 : ZMod 68103288955401349211)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (571, 1), (3697, 1), (293284993553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (571, 1), (3697, 1), (293284993553, 1)] : List FactorBlock).map factorBlockValue).prod) = 68103288955401349211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_571
      · exact prime_oneHundredFortyThreeEK_3697
      · exact prime_oneHundredFortyThreeEK_293284993553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68103288955401349211) ^ 34051644477700674605 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68103288955401349211) ^ 13620657791080269842 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68103288955401349211) ^ 6191208086854668110 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68103288955401349211) ^ 119270208328198510 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68103288955401349211) ^ 18421230445063930 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 68103288955401349211) ^ 232208570 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_71036894855462189089 : Nat.Prime 71036894855462189089 := by
  apply lucas_primality 71036894855462189089 (11 : ZMod 71036894855462189089)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (71, 1), (193, 1), (54000412664701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (71, 1), (193, 1), (54000412664701, 1)] : List FactorBlock).map factorBlockValue).prod) = 71036894855462189089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_71
      · exact prime_oneHundredFortyThreeEK_193
      · exact prime_oneHundredFortyThreeEK_54000412664701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 71036894855462189089) ^ 35518447427731094544 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 71036894855462189089) ^ 23678964951820729696 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 71036894855462189089) ^ 1000519645851580128 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 71036894855462189089) ^ 368066812722602016 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 71036894855462189089) ^ 1315488 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_105131039647847779157 : Nat.Prime 105131039647847779157 := by
  apply lucas_primality 105131039647847779157 (2 : ZMod 105131039647847779157)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) = 105131039647847779157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_173
      · exact prime_oneHundredFortyThreeEK_1831
      · exact prime_oneHundredFortyThreeEK_2676546708113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105131039647847779157) ^ 52565519823923889578 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 3391323859607992876 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 607693870796807972 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 57417279982440076 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 39278612 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_256193988611300894501 : Nat.Prime 256193988611300894501 := by
  apply lucas_primality 256193988611300894501 (2 : ZMod 256193988611300894501)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (41, 1), (4943, 1), (15683, 1), (161211241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (41, 1), (4943, 1), (15683, 1), (161211241, 1)] : List FactorBlock).map factorBlockValue).prod) = 256193988611300894501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_41
      · exact prime_oneHundredFortyThreeEK_4943
      · exact prime_oneHundredFortyThreeEK_15683
      · exact prime_oneHundredFortyThreeEK_161211241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256193988611300894501) ^ 128096994305650447250 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 256193988611300894501) ^ 51238797722260178900 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 256193988611300894501) ^ 6248633868568314500 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 256193988611300894501) ^ 51829655798361500 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 256193988611300894501) ^ 16335776867391500 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 256193988611300894501) ^ 1589181914500 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_601135034269270369663 : Nat.Prime 601135034269270369663 := by
  apply lucas_primality 601135034269270369663 (3 : ZMod 601135034269270369663)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (101, 1), (142641539, 1), (2318099881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (101, 1), (142641539, 1), (2318099881, 1)] : List FactorBlock).map factorBlockValue).prod) = 601135034269270369663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_101
      · exact prime_oneHundredFortyThreeEK_142641539
      · exact prime_oneHundredFortyThreeEK_2318099881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 601135034269270369663) ^ 300567517134635184831 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 200378344756423456554 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 5951832022468023462 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 4214305583658 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 259322317902 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1180198417187417894839 : Nat.Prime 1180198417187417894839 := by
  apply lucas_primality 1180198417187417894839 (11 : ZMod 1180198417187417894839)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (11, 1), (13, 1), (43, 1), (433, 1), (1877, 1), (2591, 1), (562621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (11, 1), (13, 1), (43, 1), (433, 1), (1877, 1), (2591, 1), (562621, 1)] : List FactorBlock).map factorBlockValue).prod) = 1180198417187417894839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_43
      · exact prime_oneHundredFortyThreeEK_433
      · exact prime_oneHundredFortyThreeEK_1877
      · exact prime_oneHundredFortyThreeEK_2591
      · exact prime_oneHundredFortyThreeEK_562621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1180198417187417894839) ^ 590099208593708947419 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1180198417187417894839) ^ 393399472395805964946 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1180198417187417894839) ^ 107290765198856172258 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1180198417187417894839) ^ 90784493629801376526 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1180198417187417894839) ^ 27446474818312044066 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1180198417187417894839) ^ 2725631448469787286 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1180198417187417894839) ^ 628768469465859294 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1180198417187417894839) ^ 455499196135630218 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 1180198417187417894839) ^ 2097679285322478 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1550411355806685423811 : Nat.Prime 1550411355806685423811 := by
  apply lucas_primality 1550411355806685423811 (2 : ZMod 1550411355806685423811)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1550411355806685423811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_3283807
      · exact prime_oneHundredFortyThreeEK_476907466417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1550411355806685423811) ^ 775205677903342711905 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 516803785268895141270 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 310082271161337084762 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 140946486891516856710 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 472138391752830 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 3250968930 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1740608115223314562877 : Nat.Prime 1740608115223314562877 := by
  apply lucas_primality 1740608115223314562877 (2 : ZMod 1740608115223314562877)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1979, 1), (2777, 1), (4003, 1), (16253, 1), (173861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1979, 1), (2777, 1), (4003, 1), (16253, 1), (173861, 1)] : List FactorBlock).map factorBlockValue).prod) = 1740608115223314562877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_1979
      · exact prime_oneHundredFortyThreeEK_2777
      · exact prime_oneHundredFortyThreeEK_4003
      · exact prime_oneHundredFortyThreeEK_16253
      · exact prime_oneHundredFortyThreeEK_173861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1740608115223314562877) ^ 870304057611657281438 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1740608115223314562877) ^ 248658302174759223268 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1740608115223314562877) ^ 879539219415520244 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1740608115223314562877) ^ 626794423919090588 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1740608115223314562877) ^ 434825909373798292 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1740608115223314562877) ^ 107094574246189292 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1740608115223314562877) ^ 10011492601695116 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2192770782028345074763 : Nat.Prime 2192770782028345074763 := by
  apply lucas_primality 2192770782028345074763 (2 : ZMod 2192770782028345074763)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (15889643348031486049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (15889643348031486049, 1)] : List FactorBlock).map factorBlockValue).prod) = 2192770782028345074763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_23
      · exact prime_oneHundredFortyThreeEK_15889643348031486049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2192770782028345074763) ^ 1096385391014172537381 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2192770782028345074763) ^ 730923594009448358254 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2192770782028345074763) ^ 95337860088188916294 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 2192770782028345074763) ^ 138 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2749603510901587471207 : Nat.Prime 2749603510901587471207 := by
  apply lucas_primality 2749603510901587471207 (5 : ZMod 2749603510901587471207)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (26956897165701837953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (26956897165701837953, 1)] : List FactorBlock).map factorBlockValue).prod) = 2749603510901587471207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_26956897165701837953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2749603510901587471207) ^ 1374801755450793735603 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2749603510901587471207) ^ 916534503633862490402 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2749603510901587471207) ^ 161741382994211027718 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 2749603510901587471207) ^ 102 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_10674341810492204540387 : Nat.Prime 10674341810492204540387 := by
  apply lucas_primality 10674341810492204540387 (2 : ZMod 10674341810492204540387)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (12739, 1), (13514938644715877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (12739, 1), (13514938644715877, 1)] : List FactorBlock).map factorBlockValue).prod) = 10674341810492204540387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_12739
      · exact prime_oneHundredFortyThreeEK_13514938644715877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10674341810492204540387) ^ 5337170905246102270193 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10674341810492204540387) ^ 344333606790071114206 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10674341810492204540387) ^ 837926195972384374 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 10674341810492204540387) ^ 789818 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_11236756836995576002141 : Nat.Prime 11236756836995576002141 := by
  apply lucas_primality 11236756836995576002141 (2 : ZMod 11236756836995576002141)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (37, 1), (5061602178826836037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (37, 1), (5061602178826836037, 1)] : List FactorBlock).map factorBlockValue).prod) = 11236756836995576002141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_37
      · exact prime_oneHundredFortyThreeEK_5061602178826836037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11236756836995576002141) ^ 5618378418497788001070 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11236756836995576002141) ^ 3745585612331858667380 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11236756836995576002141) ^ 2247351367399115200428 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11236756836995576002141) ^ 303696130729610162220 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 11236756836995576002141) ^ 2220 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_11364496833043185310417 : Nat.Prime 11364496833043185310417 := by
  apply lucas_primality 11364496833043185310417 (5 : ZMod 11364496833043185310417)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (3160157971, 1), (10702916611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (3160157971, 1), (10702916611, 1)] : List FactorBlock).map factorBlockValue).prod) = 11364496833043185310417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_3160157971
      · exact prime_oneHundredFortyThreeEK_10702916611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11364496833043185310417) ^ 5682248416521592655208 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 11364496833043185310417) ^ 3788165611014395103472 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 11364496833043185310417) ^ 1623499547577597901488 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 11364496833043185310417) ^ 3596179981296 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 11364496833043185310417) ^ 1061813078256 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_14608894583142498119419 : Nat.Prime 14608894583142498119419 := by
  apply lucas_primality 14608894583142498119419 (3 : ZMod 14608894583142498119419)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 2), (103213379, 1), (3886985953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 2), (103213379, 1), (3886985953, 1)] : List FactorBlock).map factorBlockValue).prod) = 14608894583142498119419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_103213379
      · exact prime_oneHundredFortyThreeEK_3886985953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14608894583142498119419) ^ 7304447291571249059709 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 14608894583142498119419) ^ 4869631527714166039806 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 14608894583142498119419) ^ 2086984940448928302774 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 14608894583142498119419) ^ 859346740184852830554 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 14608894583142498119419) ^ 141540706492542 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 14608894583142498119419) ^ 3758411982906 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_18058827904197170191141 : Nat.Prime 18058827904197170191141 := by
  apply lucas_primality 18058827904197170191141 (2 : ZMod 18058827904197170191141)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (23, 1), (29, 1), (797, 1), (43552270540237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (23, 1), (29, 1), (797, 1), (43552270540237, 1)] : List FactorBlock).map factorBlockValue).prod) = 18058827904197170191141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_23
      · exact prime_oneHundredFortyThreeEK_29
      · exact prime_oneHundredFortyThreeEK_797
      · exact prime_oneHundredFortyThreeEK_43552270540237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18058827904197170191141) ^ 9029413952098585095570 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 18058827904197170191141) ^ 6019609301399056730380 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 18058827904197170191141) ^ 3611765580839434038228 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 18058827904197170191141) ^ 1389140608015166937780 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 18058827904197170191141) ^ 785166430617268269180 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 18058827904197170191141) ^ 622718203593005868660 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 18058827904197170191141) ^ 22658504271263701620 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 18058827904197170191141) ^ 414647220 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_22077934052866587991201 : Nat.Prime 22077934052866587991201 := by
  apply lucas_primality 22077934052866587991201 (11 : ZMod 22077934052866587991201)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (7, 1), (17, 1), (131, 1), (4889, 1), (338323, 1), (356761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (7, 1), (17, 1), (131, 1), (4889, 1), (338323, 1), (356761, 1)] : List FactorBlock).map factorBlockValue).prod) = 22077934052866587991201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_131
      · exact prime_oneHundredFortyThreeEK_4889
      · exact prime_oneHundredFortyThreeEK_338323
      · exact prime_oneHundredFortyThreeEK_356761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 22077934052866587991201) ^ 11038967026433293995600 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22077934052866587991201) ^ 7359311350955529330400 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22077934052866587991201) ^ 4415586810573317598240 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22077934052866587991201) ^ 3153990578980941141600 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22077934052866587991201) ^ 1298702003109799293600 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22077934052866587991201) ^ 168533847731806015200 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22077934052866587991201) ^ 4515838423576720800 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22077934052866587991201) ^ 65256970566194400 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 22077934052866587991201) ^ 61884382129399200 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_35853529750253765128927 : Nat.Prime 35853529750253765128927 := by
  apply lucas_primality 35853529750253765128927 (3 : ZMod 35853529750253765128927)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853529750253765128927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_71
      · exact prime_oneHundredFortyThreeEK_8317
      · exact prime_oneHundredFortyThreeEK_66139999399751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853529750253765128927) ^ 17926764875126882564463 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 11951176583417921709642 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 2109031161779633242878 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 504979292257095283506 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 4310872880876970678 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 542085426 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_215121178501522590773563 : Nat.Prime 215121178501522590773563 := by
  apply lucas_primality 215121178501522590773563 (2 : ZMod 215121178501522590773563)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) = 215121178501522590773563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_35853529750253765128927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 215121178501522590773563) ^ 107560589250761295386781 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 71707059500507530257854 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 6 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_314773401551865036053243 : Nat.Prime 314773401551865036053243 := by
  apply lucas_primality 314773401551865036053243 (2 : ZMod 314773401551865036053243)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2311, 1), (68103288955401349211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2311, 1), (68103288955401349211, 1)] : List FactorBlock).map factorBlockValue).prod) = 314773401551865036053243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_2311
      · exact prime_oneHundredFortyThreeEK_68103288955401349211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 314773401551865036053243) ^ 157386700775932518026621 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 314773401551865036053243) ^ 136206577910802698422 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 314773401551865036053243) ^ 4622 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_502198630102372826020427 : Nat.Prime 502198630102372826020427 := by
  apply lucas_primality 502198630102372826020427 (6 : ZMod 502198630102372826020427)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 2), (2143, 1), (46367973446495333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 2), (2143, 1), (46367973446495333, 1)] : List FactorBlock).map factorBlockValue).prod) = 502198630102372826020427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_19
      · exact prime_oneHundredFortyThreeEK_2143
      · exact prime_oneHundredFortyThreeEK_46367973446495333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 502198630102372826020427) ^ 251099315051186413010213 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 502198630102372826020427) ^ 71742661443196118002918 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 502198630102372826020427) ^ 26431506847493306632654 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 502198630102372826020427) ^ 234343737798587412982 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 502198630102372826020427) ^ 10830722 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_965341763602176659781223 : Nat.Prime 965341763602176659781223 := by
  apply lucas_primality 965341763602176659781223 (3 : ZMod 965341763602176659781223)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (17, 1), (79, 1), (28415539, 1), (66920223787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (17, 1), (79, 1), (28415539, 1), (66920223787, 1)] : List FactorBlock).map factorBlockValue).prod) = 965341763602176659781223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_79
      · exact prime_oneHundredFortyThreeEK_28415539
      · exact prime_oneHundredFortyThreeEK_66920223787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 965341763602176659781223) ^ 482670881801088329890611 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 965341763602176659781223) ^ 321780587867392219927074 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 965341763602176659781223) ^ 137905966228882379968746 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 965341763602176659781223) ^ 56784809623657450575366 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 965341763602176659781223) ^ 12219515994964261516218 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 965341763602176659781223) ^ 33972319286365698 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 965341763602176659781223) ^ 14425262035506 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1932471074534252419062761 : Nat.Prime 1932471074534252419062761 := by
  apply lucas_primality 1932471074534252419062761 (3 : ZMod 1932471074534252419062761)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (26177599013, 1), (1845538883813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (26177599013, 1), (1845538883813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1932471074534252419062761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_26177599013
      · exact prime_oneHundredFortyThreeEK_1845538883813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1932471074534252419062761) ^ 966235537267126209531380 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932471074534252419062761) ^ 386494214906850483812552 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932471074534252419062761) ^ 73821555352520 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932471074534252419062761) ^ 1047103960520 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_2318265723623673085882111 : Nat.Prime 2318265723623673085882111 := by
  apply lucas_primality 2318265723623673085882111 (3 : ZMod 2318265723623673085882111)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (29, 1), (1470847129, 1), (603886289519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (29, 1), (1470847129, 1), (603886289519, 1)] : List FactorBlock).map factorBlockValue).prod) = 2318265723623673085882111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_29
      · exact prime_oneHundredFortyThreeEK_1470847129
      · exact prime_oneHundredFortyThreeEK_603886289519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2318265723623673085882111) ^ 1159132861811836542941055 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2318265723623673085882111) ^ 772755241207891028627370 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2318265723623673085882111) ^ 463653144724734617176422 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2318265723623673085882111) ^ 79940197366333554685590 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2318265723623673085882111) ^ 1576143215644590 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 2318265723623673085882111) ^ 3838911006690 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_60250949546223666120500609 : Nat.Prime 60250949546223666120500609 := by
  apply lucas_primality 60250949546223666120500609 (3 : ZMod 60250949546223666120500609)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (37, 1), (4691, 1), (209497, 1), (12945205849789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (37, 1), (4691, 1), (209497, 1), (12945205849789, 1)] : List FactorBlock).map factorBlockValue).prod) = 60250949546223666120500609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_37
      · exact prime_oneHundredFortyThreeEK_4691
      · exact prime_oneHundredFortyThreeEK_209497
      · exact prime_oneHundredFortyThreeEK_12945205849789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 60250949546223666120500609) ^ 30125474773111833060250304 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 60250949546223666120500609) ^ 1628404041789828814067584 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 60250949546223666120500609) ^ 12843945757029133685888 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 60250949546223666120500609) ^ 287598149597481902464 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 60250949546223666120500609) ^ 4654306022272 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_105929927585653889181782399 : Nat.Prime 105929927585653889181782399 := by
  apply lucas_primality 105929927585653889181782399 (7 : ZMod 105929927585653889181782399)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2399, 1), (22077934052866587991201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2399, 1), (22077934052866587991201, 1)] : List FactorBlock).map factorBlockValue).prod) = 105929927585653889181782399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_2399
      · exact prime_oneHundredFortyThreeEK_22077934052866587991201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 105929927585653889181782399) ^ 52964963792826944590891199 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 105929927585653889181782399) ^ 44155868105733175982402 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (7 : ZMod 105929927585653889181782399) ^ 4798 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_107342326620129274370872831 : Nat.Prime 107342326620129274370872831 := by
  apply lucas_primality 107342326620129274370872831 (3 : ZMod 107342326620129274370872831)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (41, 1), (444611747, 1), (3848706415793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (41, 1), (444611747, 1), (3848706415793, 1)] : List FactorBlock).map factorBlockValue).prod) = 107342326620129274370872831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_41
      · exact prime_oneHundredFortyThreeEK_444611747
      · exact prime_oneHundredFortyThreeEK_3848706415793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 107342326620129274370872831) ^ 53671163310064637185436415 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 107342326620129274370872831) ^ 35780775540043091456957610 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 107342326620129274370872831) ^ 21468465324025854874174566 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 107342326620129274370872831) ^ 6314254507066427904168990 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 107342326620129274370872831) ^ 2618105527320226204167630 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 107342326620129274370872831) ^ 241429353462694890 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 107342326620129274370872831) ^ 27890494889310 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_391352232469221312810473863 : Nat.Prime 391352232469221312810473863 := by
  apply lucas_primality 391352232469221312810473863 (11 : ZMod 391352232469221312810473863)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (89, 1), (131, 1), (1031, 1), (11352647, 1), (1750801123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (89, 1), (131, 1), (1031, 1), (11352647, 1), (1750801123, 1)] : List FactorBlock).map factorBlockValue).prod) = 391352232469221312810473863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_7
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_89
      · exact prime_oneHundredFortyThreeEK_131
      · exact prime_oneHundredFortyThreeEK_1031
      · exact prime_oneHundredFortyThreeEK_11352647
      · exact prime_oneHundredFortyThreeEK_1750801123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 391352232469221312810473863) ^ 195676116234610656405236931 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 391352232469221312810473863) ^ 130450744156407104270157954 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 391352232469221312810473863) ^ 55907461781317330401496266 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 391352232469221312810473863) ^ 30104017882247793293113374 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 391352232469221312810473863) ^ 4397216095159790031578358 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 391352232469221312810473863) ^ 2987421621902452769545602 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 391352232469221312810473863) ^ 379585094538526976537802 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 391352232469221312810473863) ^ 34472333409928214346 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 391352232469221312810473863) ^ 223527519675472194 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_1018458821847612091169425957 : Nat.Prime 1018458821847612091169425957 := by
  apply lucas_primality 1018458821847612091169425957 (2 : ZMod 1018458821847612091169425957)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (502198630102372826020427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (502198630102372826020427, 1)] : List FactorBlock).map factorBlockValue).prod) = 1018458821847612091169425957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_502198630102372826020427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1018458821847612091169425957) ^ 509229410923806045584712978 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1018458821847612091169425957) ^ 339486273949204030389808652 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1018458821847612091169425957) ^ 78342986295970160859186612 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 1018458821847612091169425957) ^ 2028 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_6502467862565523351312488803 : Nat.Prime 6502467862565523351312488803 := by
  apply lucas_primality 6502467862565523351312488803 (2 : ZMod 6502467862565523351312488803)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 6502467862565523351312488803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_107
      · exact prime_oneHundredFortyThreeEK_43001837
      · exact prime_oneHundredFortyThreeEK_78511797954027271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6502467862565523351312488803) ^ 3251233931282761675656244401 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 2167489287521841117104162934 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 60770727687528255619742886 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 151213722859456523946 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 82821538062 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_18784907158522623014902745423 : Nat.Prime 18784907158522623014902745423 := by
  apply lucas_primality 18784907158522623014902745423 (5 : ZMod 18784907158522623014902745423)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11953, 1), (32213, 1), (24393322929934562299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11953, 1), (32213, 1), (24393322929934562299, 1)] : List FactorBlock).map factorBlockValue).prod) = 18784907158522623014902745423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_11953
      · exact prime_oneHundredFortyThreeEK_32213
      · exact prime_oneHundredFortyThreeEK_24393322929934562299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18784907158522623014902745423) ^ 9392453579261311507451372711 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18784907158522623014902745423) ^ 1571564223083964110675374 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18784907158522623014902745423) ^ 583146777963015646319894 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 18784907158522623014902745423) ^ 770083978 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_33812832885340721426824941763 : Nat.Prime 33812832885340721426824941763 := by
  apply lucas_primality 33812832885340721426824941763 (2 : ZMod 33812832885340721426824941763)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (452849659, 1), (12444465918338666353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (452849659, 1), (12444465918338666353, 1)] : List FactorBlock).map factorBlockValue).prod) = 33812832885340721426824941763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_452849659
      · exact prime_oneHundredFortyThreeEK_12444465918338666353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33812832885340721426824941763) ^ 16906416442670360713412470881 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 33812832885340721426824941763) ^ 11270944295113573808941647254 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 33812832885340721426824941763) ^ 74666795510031998118 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 33812832885340721426824941763) ^ 2717097954 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_33812832885340721426824941767 : Nat.Prime 33812832885340721426824941767 := by
  apply lucas_primality 33812832885340721426824941767 (5 : ZMod 33812832885340721426824941767)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (59, 1), (103, 1), (1201, 1), (3928753, 1), (19019666571553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (59, 1), (103, 1), (1201, 1), (3928753, 1), (19019666571553, 1)] : List FactorBlock).map factorBlockValue).prod) = 33812832885340721426824941767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_31
      · exact prime_oneHundredFortyThreeEK_59
      · exact prime_oneHundredFortyThreeEK_103
      · exact prime_oneHundredFortyThreeEK_1201
      · exact prime_oneHundredFortyThreeEK_3928753
      · exact prime_oneHundredFortyThreeEK_19019666571553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33812832885340721426824941767) ^ 16906416442670360713412470883 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 33812832885340721426824941767) ^ 1090736544688410368607256186 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 33812832885340721426824941767) ^ 573098862463402058081778674 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 33812832885340721426824941767) ^ 328279930925638072105096522 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 33812832885340721426824941767) ^ 28153899155154638989862566 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 33812832885340721426824941767) ^ 8606505139249202336422 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (5 : ZMod 33812832885340721426824941767) ^ 1777782631369222 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_42266041106675901783531177217 : Nat.Prime 42266041106675901783531177217 := by
  apply lucas_primality 42266041106675901783531177217 (10 : ZMod 42266041106675901783531177217)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (353, 1), (251893, 1), (4040789, 1), (153169880527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (353, 1), (251893, 1), (4040789, 1), (153169880527, 1)] : List FactorBlock).map factorBlockValue).prod) = 42266041106675901783531177217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_353
      · exact prime_oneHundredFortyThreeEK_251893
      · exact prime_oneHundredFortyThreeEK_4040789
      · exact prime_oneHundredFortyThreeEK_153169880527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 42266041106675901783531177217) ^ 21133020553337950891765588608 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 42266041106675901783531177217) ^ 14088680368891967261177059072 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 42266041106675901783531177217) ^ 119733827497665444145980672 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 42266041106675901783531177217) ^ 167793631052375023456512 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 42266041106675901783531177217) ^ 10459848585678663692544 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (10 : ZMod 42266041106675901783531177217) ^ 275942247661579008 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_56354721475567869044708236291 : Nat.Prime 56354721475567869044708236291 := by
  apply lucas_primality 56354721475567869044708236291 (3 : ZMod 56354721475567869044708236291)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (4111, 1), (35160493427, 1), (481329911297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (4111, 1), (35160493427, 1), (481329911297, 1)] : List FactorBlock).map factorBlockValue).prod) = 56354721475567869044708236291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_4111
      · exact prime_oneHundredFortyThreeEK_35160493427
      · exact prime_oneHundredFortyThreeEK_481329911297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56354721475567869044708236291) ^ 28177360737783934522354118145 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56354721475567869044708236291) ^ 18784907158522623014902745430 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56354721475567869044708236291) ^ 11270944295113573808941647258 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56354721475567869044708236291) ^ 13708275717725095851303390 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56354721475567869044708236291) ^ 1602785284926993270 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (3 : ZMod 56354721475567869044708236291) ^ 117081278667501570 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_84532082213351803567062354401 : Nat.Prime 84532082213351803567062354401 := by
  apply lucas_primality 84532082213351803567062354401 (6 : ZMod 84532082213351803567062354401)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (11, 1), (13, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (11, 1), (13, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 84532082213351803567062354401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_11
      · exact prime_oneHundredFortyThreeEK_13
      · exact prime_oneHundredFortyThreeEK_171401
      · exact prime_oneHundredFortyThreeEK_714027719
      · exact prime_oneHundredFortyThreeEK_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 84532082213351803567062354401) ^ 42266041106675901783531177200 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 84532082213351803567062354401) ^ 16906416442670360713412470880 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 84532082213351803567062354401) ^ 7684734746668345778823850400 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 84532082213351803567062354401) ^ 6502467862565523351312488800 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 84532082213351803567062354401) ^ 493183133198474942194400 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 84532082213351803567062354401) ^ 118387675945885517600 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (6 : ZMod 84532082213351803567062354401) ^ 14000851443358093600 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_169064164426703607134124708841 : Nat.Prime 169064164426703607134124708841 := by
  apply lucas_primality 169064164426703607134124708841 (11 : ZMod 169064164426703607134124708841)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (151, 1), (821, 1), (11364496833043185310417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (151, 1), (821, 1), (11364496833043185310417, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_5
      · exact prime_oneHundredFortyThreeEK_151
      · exact prime_oneHundredFortyThreeEK_821
      · exact prime_oneHundredFortyThreeEK_11364496833043185310417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 169064164426703607134124708841) ^ 84532082213351803567062354420 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 169064164426703607134124708841) ^ 56354721475567869044708236280 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 169064164426703607134124708841) ^ 33812832885340721426824941768 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 169064164426703607134124708841) ^ 1119630227991414616782282840 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 169064164426703607134124708841) ^ 205924682614742517824756040 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (11 : ZMod 169064164426703607134124708841) ^ 14876520 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyThreeEK_169064164426703607134124708883 : Nat.Prime 169064164426703607134124708883 := by
  apply lucas_primality 169064164426703607134124708883 (2 : ZMod 169064164426703607134124708883)
  · rw [← oneHundredFortyThreeEKFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (101, 1), (965341763602176659781223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (101, 1), (965341763602176659781223, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyThreeEK_2
      · exact prime_oneHundredFortyThreeEK_3
      · exact prime_oneHundredFortyThreeEK_17
      · exact prime_oneHundredFortyThreeEK_101
      · exact prime_oneHundredFortyThreeEK_965341763602176659781223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 169064164426703607134124708883) ^ 84532082213351803567062354441 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 169064164426703607134124708883) ^ 56354721475567869044708236294 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 169064164426703607134124708883) ^ 9944950848629623949066159346 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 169064164426703607134124708883) ^ 1673902618086174328060640682 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide
    · change (2 : ZMod 169064164426703607134124708883) ^ 175134 ≠ 1
      rw [← oneHundredFortyThreeEKFastPow_eq_pow]
      decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708800 : Nat.totient 169064164426703607134124708800 = 56748479260082249026990080000 := by
  rw [← show ((([(2, 6), (5, 2), (11, 1), (13, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_11, prime_oneHundredFortyThreeEK_13, prime_oneHundredFortyThreeEK_171401, prime_oneHundredFortyThreeEK_714027719, prime_oneHundredFortyThreeEK_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708801 : Nat.totient 169064164426703607134124708801 = 112709437451928716286200538960 := by
  rw [← show ((([(3, 1), (20495581, 1), (2749603510901587471207, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_20495581, prime_oneHundredFortyThreeEK_2749603510901587471207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708802 : Nat.totient 169064164426703607134124708802 = 84532082213351803567062354400 := by
  rw [← show ((([(2, 1), (84532082213351803567062354401, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_84532082213351803567062354401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708803 : Nat.totient 169064164426703607134124708803 = 169064153752361796641904330048 := by
  rw [← show ((([(15838369, 1), (10674341810492204540387, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_15838369, prime_oneHundredFortyThreeEK_10674341810492204540387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708804 : Nat.totient 169064164426703607134124708804 = 45761728717002480126529995936 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (19, 1), (105929927585653889181782399, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_19, prime_oneHundredFortyThreeEK_105929927585653889181782399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708805 : Nat.totient 169064164426703607134124708805 = 133346383050606769017346498560 := by
  rw [← show ((([(5, 1), (71, 1), (837668023, 1), (568527232526486017, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_71, prime_oneHundredFortyThreeEK_837668023, prime_oneHundredFortyThreeEK_568527232526486017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708806 : Nat.totient 169064164426703607134124708806 = 84330322793860943185922210400 := by
  rw [← show ((([(2, 1), (419, 1), (6926357, 1), (5129457031, 1), (5678469211, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_419, prime_oneHundredFortyThreeEK_6926357, prime_oneHundredFortyThreeEK_5129457031, prime_oneHundredFortyThreeEK_5678469211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708807 : Nat.totient 169064164426703607134124708807 = 112709442951135738089416472532 := by
  rw [← show ((([(3, 2), (18784907158522623014902745423, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_18784907158522623014902745423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708808 : Nat.totient 169064164426703607134124708808 = 77048176645490125412330864640 := by
  rw [← show ((([(2, 3), (23, 1), (41, 1), (43, 1), (39509, 1), (18880633, 1), (698664761017, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_23, prime_oneHundredFortyThreeEK_41, prime_oneHundredFortyThreeEK_43, prime_oneHundredFortyThreeEK_39509, prime_oneHundredFortyThreeEK_18880633, prime_oneHundredFortyThreeEK_698664761017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708809 : Nat.totient 169064164426703607134124708809 = 169062390698835145517391250800 := by
  rw [← show ((([(95317, 1), (7146931927, 1), (248177012270051, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_95317, prime_oneHundredFortyThreeEK_7146931927, prime_oneHundredFortyThreeEK_248177012270051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708810 : Nat.totient 169064164426703607134124708810 = 45083777080898567885434460928 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (452849659, 1), (12444465918338666353, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_452849659, prime_oneHundredFortyThreeEK_12444465918338666353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708811 : Nat.totient 169064164426703607134124708811 = 131309219685912858985076098560 := by
  rw [← show ((([(7, 1), (11, 2), (317, 1), (9719, 1), (6998309863, 1), (9257508937, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_11, prime_oneHundredFortyThreeEK_317, prime_oneHundredFortyThreeEK_9719, prime_oneHundredFortyThreeEK_6998309863, prime_oneHundredFortyThreeEK_9257508937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708812 : Nat.totient 169064164426703607134124708812 = 82987654493941158062134185984 := by
  rw [← show ((([(2, 2), (79, 1), (193, 1), (1979, 1), (588708059, 1), (2379366789509, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_79, prime_oneHundredFortyThreeEK_193, prime_oneHundredFortyThreeEK_1979, prime_oneHundredFortyThreeEK_588708059, prime_oneHundredFortyThreeEK_2379366789509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708813 : Nat.totient 169064164426703607134124708813 = 104029049424960750993390673920 := by
  rw [← show ((([(3, 1), (13, 1), (18541, 1), (21617, 1), (8348687, 1), (1295508299753, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_13, prime_oneHundredFortyThreeEK_18541, prime_oneHundredFortyThreeEK_21617, prime_oneHundredFortyThreeEK_8348687, prime_oneHundredFortyThreeEK_1295508299753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708814 : Nat.totient 169064164426703607134124708814 = 79554570414612161751952170112 := by
  rw [← show ((([(2, 1), (17, 1), (15797, 1), (314773401551865036053243, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_17, prime_oneHundredFortyThreeEK_15797, prime_oneHundredFortyThreeEK_314773401551865036053243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708815 : Nat.totient 169064164426703607134124708815 = 135251331541362885707299767048 := by
  rw [← show ((([(5, 1), (33812832885340721426824941763, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_33812832885340721426824941763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708816 : Nat.totient 169064164426703607134124708816 = 56354721475567869044708236128 := by
  rw [← show ((([(2, 4), (3, 3), (391352232469221312810473863, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_391352232469221312810473863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708817 : Nat.totient 169064164426703607134124708817 = 168084982199170975645707181440 := by
  rw [← show ((([(173, 1), (86969, 1), (11236756836995576002141, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_173, prime_oneHundredFortyThreeEK_86969, prime_oneHundredFortyThreeEK_11236756836995576002141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708818 : Nat.totient 169064164426703607134124708818 = 69848786510401670200059789312 := by
  rw [← show ((([(2, 1), (7, 1), (29, 1), (643, 1), (1904583937, 1), (340027810279433, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_29, prime_oneHundredFortyThreeEK_643, prime_oneHundredFortyThreeEK_1904583937, prime_oneHundredFortyThreeEK_340027810279433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708819 : Nat.totient 169064164426703607134124708819 = 112704335330800634587979309952 := by
  rw [← show ((([(3, 1), (23557, 1), (349483, 1), (192313427, 1), (35593825229, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_23557, prime_oneHundredFortyThreeEK_349483, prime_oneHundredFortyThreeEK_192313427, prime_oneHundredFortyThreeEK_35593825229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708820 : Nat.totient 169064164426703607134124708820 = 66931769772260615226248552448 := by
  rw [← show ((([(2, 2), (5, 1), (113, 1), (877, 1), (5059, 1), (11587, 1), (1455150267657277, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_113, prime_oneHundredFortyThreeEK_877, prime_oneHundredFortyThreeEK_5059, prime_oneHundredFortyThreeEK_11587, prime_oneHundredFortyThreeEK_1455150267657277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708821 : Nat.totient 169064164426703607134124708821 = 169064164425334192088698830144 := by
  rw [← show ((([(123457223749, 1), (1369414921968654929, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_123457223749, prime_oneHundredFortyThreeEK_1369414921968654929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708822 : Nat.totient 169064164426703607134124708822 = 50862992079045647619277927200 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (139, 1), (104050223, 1), (177112743868002511, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_11, prime_oneHundredFortyThreeEK_139, prime_oneHundredFortyThreeEK_104050223, prime_oneHundredFortyThreeEK_177112743868002511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708823 : Nat.totient 169064164426703607134124708823 = 155837228949180825704216102016 := by
  rw [← show ((([(19, 1), (37, 1), (16605997, 1), (14482091339026052653, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_19, prime_oneHundredFortyThreeEK_37, prime_oneHundredFortyThreeEK_16605997, prime_oneHundredFortyThreeEK_14482091339026052653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708824 : Nat.totient 169064164426703607134124708824 = 81799995039229548068659117056 := by
  rw [← show ((([(2, 3), (53, 1), (73, 1), (80429, 1), (67912571720353889203, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_53, prime_oneHundredFortyThreeEK_73, prime_oneHundredFortyThreeEK_80429, prime_oneHundredFortyThreeEK_67912571720353889203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708825 : Nat.totient 169064164426703607134124708825 = 77286475166493077547028437600 := by
  rw [← show ((([(3, 2), (5, 2), (7, 1), (107342326620129274370872831, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_107342326620129274370872831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708826 : Nat.totient 169064164426703607134124708826 = 77133849763505940147768390720 := by
  rw [← show ((([(2, 1), (13, 1), (167, 1), (181, 1), (215121178501522590773563, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_13, prime_oneHundredFortyThreeEK_167, prime_oneHundredFortyThreeEK_181, prime_oneHundredFortyThreeEK_215121178501522590773563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708827 : Nat.totient 169064164426703607134124708827 = 169064069811426232791180086664 := by
  rw [← show ((([(2060099, 1), (13472059, 1), (6091573588046347, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2060099, prime_oneHundredFortyThreeEK_13472059, prime_oneHundredFortyThreeEK_6091573588046347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708828 : Nat.totient 169064164426703607134124708828 = 56354709443575886126408024064 := by
  rw [← show ((([(2, 2), (3, 1), (4724353, 1), (544894729, 1), (5472872986837, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_4724353, prime_oneHundredFortyThreeEK_544894729, prime_oneHundredFortyThreeEK_5472872986837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708829 : Nat.totient 169064164426703607134124708829 = 167078885474334079971258019200 := by
  rw [← show ((([(89, 1), (1951, 1), (1398517567, 1), (696203753478533, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_89, prime_oneHundredFortyThreeEK_1951, prime_oneHundredFortyThreeEK_1398517567, prime_oneHundredFortyThreeEK_696203753478533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708830 : Nat.totient 169064164426703607134124708830 = 63657293765039087230550016000 := by
  rw [← show ((([(2, 1), (5, 1), (31, 1), (59, 1), (103, 1), (1201, 1), (3928753, 1), (19019666571553, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_31, prime_oneHundredFortyThreeEK_59, prime_oneHundredFortyThreeEK_103, prime_oneHundredFortyThreeEK_1201, prime_oneHundredFortyThreeEK_3928753, prime_oneHundredFortyThreeEK_19019666571553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708831 : Nat.totient 169064164426703607134124708831 = 101430612665900457099408883712 := by
  rw [← show ((([(3, 1), (17, 1), (23, 1), (2903, 1), (57653, 1), (861161495993700833, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_17, prime_oneHundredFortyThreeEK_23, prime_oneHundredFortyThreeEK_2903, prime_oneHundredFortyThreeEK_57653, prime_oneHundredFortyThreeEK_861161495993700833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708832 : Nat.totient 169064164426703607134124708832 = 72456070443899058624734644608 := by
  rw [← show ((([(2, 5), (7, 1), (2934846067, 1), (257168763477700979, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_2934846067, prime_oneHundredFortyThreeEK_257168763477700979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708833 : Nat.totient 169064164426703607134124708833 = 150423636251552564632734984960 := by
  rw [← show ((([(11, 1), (47, 1), (160183, 1), (7631857, 1), (267494201311979, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_11, prime_oneHundredFortyThreeEK_47, prime_oneHundredFortyThreeEK_160183, prime_oneHundredFortyThreeEK_7631857, prime_oneHundredFortyThreeEK_267494201311979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708834 : Nat.totient 169064164426703607134124708834 = 56354574184529812416220439808 := by
  rw [← show ((([(2, 1), (3, 2), (384533, 1), (76426429, 1), (319596396058409, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_384533, prime_oneHundredFortyThreeEK_76426429, prime_oneHundredFortyThreeEK_319596396058409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708835 : Nat.totient 169064164426703607134124708835 = 135251331541362885707299767064 := by
  rw [← show ((([(5, 1), (33812832885340721426824941767, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_33812832885340721426824941767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708836 : Nat.totient 169064164426703607134124708836 = 84532081700963826344130612000 := by
  rw [← show ((([(2, 2), (164976709, 1), (256193988611300894501, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_164976709, prime_oneHundredFortyThreeEK_256193988611300894501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708837 : Nat.totient 169064164426703607134124708837 = 112709406833479929695069849040 := by
  rw [← show ((([(3, 1), (3120619, 1), (18058827904197170191141, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_3120619, prime_oneHundredFortyThreeEK_18058827904197170191141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708838 : Nat.totient 169064164426703607134124708838 = 84529389659323186726795091200 := by
  rw [← show ((([(2, 1), (42281, 1), (121931, 1), (16396916337010523729, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_42281, prime_oneHundredFortyThreeEK_121931, prime_oneHundredFortyThreeEK_16396916337010523729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708839 : Nat.totient 169064164426703607134124708839 = 133765053148141073245889723232 := by
  rw [← show ((([(7, 3), (13, 1), (5429792839, 1), (6982819718723939, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_13, prime_oneHundredFortyThreeEK_5429792839, prime_oneHundredFortyThreeEK_6982819718723939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708840 : Nat.totient 169064164426703607134124708840 = 44730659534857977381797376000 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (151, 1), (821, 1), (11364496833043185310417, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_151, prime_oneHundredFortyThreeEK_821, prime_oneHundredFortyThreeEK_11364496833043185310417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708841 : Nat.totient 169064164426703607134124708841 = 169064164426703607134124708840 := by
  rw [← show ((([(169064164426703607134124708841, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_169064164426703607134124708841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708842 : Nat.totient 169064164426703607134124708842 = 80066938287086513212561070400 := by
  rw [← show ((([(2, 1), (19, 1), (8539, 1), (13669, 1), (94151, 1), (404854780352999, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_19, prime_oneHundredFortyThreeEK_8539, prime_oneHundredFortyThreeEK_13669, prime_oneHundredFortyThreeEK_94151, prime_oneHundredFortyThreeEK_404854780352999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708843 : Nat.totient 169064164426703607134124708843 = 112387854563434128483773337600 := by
  rw [← show ((([(3, 3), (617, 1), (811, 1), (696743, 1), (39162769, 1), (458601821, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_617, prime_oneHundredFortyThreeEK_811, prime_oneHundredFortyThreeEK_696743, prime_oneHundredFortyThreeEK_39162769, prime_oneHundredFortyThreeEK_458601821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708844 : Nat.totient 169064164426703607134124708844 = 76847347466680484684575549440 := by
  rw [← show ((([(2, 2), (11, 1), (33312673606897, 1), (115342509540833, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_11, prime_oneHundredFortyThreeEK_33312673606897, prime_oneHundredFortyThreeEK_115342509540833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708845 : Nat.totient 169064164426703607134124708845 = 133232654610850854611670490944 := by
  rw [← show ((([(5, 1), (67, 1), (391466479, 1), (1289175892739461933, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_67, prime_oneHundredFortyThreeEK_391466479, prime_oneHundredFortyThreeEK_1289175892739461933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708846 : Nat.totient 169064164426703607134124708846 = 48280857326163762437863995840 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (2083, 1), (1932471074534252419062761, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_2083, prime_oneHundredFortyThreeEK_1932471074534252419062761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708847 : Nat.totient 169064164426703607134124708847 = 162735427521281720382451574400 := by
  rw [← show ((([(29, 1), (443, 1), (1451, 1), (8933, 1), (1015278271831597447, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_29, prime_oneHundredFortyThreeEK_443, prime_oneHundredFortyThreeEK_1451, prime_oneHundredFortyThreeEK_8933, prime_oneHundredFortyThreeEK_1015278271831597447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708848 : Nat.totient 169064164426703607134124708848 = 79030794371289153005825372160 := by
  rw [← show ((([(2, 4), (17, 1), (157, 1), (3583, 1), (5444978771, 1), (202927080359, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_17, prime_oneHundredFortyThreeEK_157, prime_oneHundredFortyThreeEK_3583, prime_oneHundredFortyThreeEK_5444978771, prime_oneHundredFortyThreeEK_202927080359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708849 : Nat.totient 169064164426703607134124708849 = 109551611429446820490072192000 := by
  rw [← show ((([(3, 1), (41, 1), (269, 1), (2387927, 1), (2139799712767801801, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_41, prime_oneHundredFortyThreeEK_269, prime_oneHundredFortyThreeEK_2387927, prime_oneHundredFortyThreeEK_2139799712767801801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708850 : Nat.totient 169064164426703607134124708850 = 67625665770677039702012549520 := by
  rw [← show ((([(2, 1), (5, 2), (16611914849819, 1), (203545667016883, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_16611914849819, prime_oneHundredFortyThreeEK_203545667016883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708851 : Nat.totient 169064164426703607134124708851 = 164905297368820880705518142304 := by
  rw [← show ((([(43, 1), (727, 1), (7902610643, 1), (684349746850837, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_43, prime_oneHundredFortyThreeEK_727, prime_oneHundredFortyThreeEK_7902610643, prime_oneHundredFortyThreeEK_684349746850837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708852 : Nat.totient 169064164426703607134124708852 = 51533575880619876138889678080 := by
  rw [← show ((([(2, 2), (3, 2), (13, 1), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_13, prime_oneHundredFortyThreeEK_107, prime_oneHundredFortyThreeEK_43001837, prime_oneHundredFortyThreeEK_78511797954027271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708853 : Nat.totient 169064164426703607134124708853 = 144253951800625618290396143856 := by
  rw [← show ((([(7, 1), (227, 1), (7283, 1), (14608894583142498119419, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_227, prime_oneHundredFortyThreeEK_7283, prime_oneHundredFortyThreeEK_14608894583142498119419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708854 : Nat.totient 169064164426703607134124708854 = 79531253401015239279060802560 := by
  rw [← show ((([(2, 1), (23, 1), (61, 1), (60250949546223666120500609, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_23, prime_oneHundredFortyThreeEK_61, prime_oneHundredFortyThreeEK_60250949546223666120500609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708855 : Nat.totient 169064164426703607134124708855 = 81970503730258822606384231680 := by
  rw [← show ((([(3, 1), (5, 1), (11, 1), (349996873, 1), (2927544154246713619, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_11, prime_oneHundredFortyThreeEK_349996873, prime_oneHundredFortyThreeEK_2927544154246713619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708856 : Nat.totient 169064164426703607134124708856 = 84510565472089471687921872000 := by
  rw [← show ((([(2, 3), (4231, 1), (55691, 1), (4224991, 1), (21227934830437, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_4231, prime_oneHundredFortyThreeEK_55691, prime_oneHundredFortyThreeEK_4224991, prime_oneHundredFortyThreeEK_21227934830437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708857 : Nat.totient 169064164426703607134124708857 = 168957502151771793609556818048 := by
  rw [← show ((([(2539, 1), (4217, 1), (3014317637, 1), (5238370908647, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2539, prime_oneHundredFortyThreeEK_4217, prime_oneHundredFortyThreeEK_3014317637, prime_oneHundredFortyThreeEK_5238370908647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708858 : Nat.totient 169064164426703607134124708858 = 55773738552388862183740434432 := by
  rw [← show ((([(2, 1), (3, 1), (97, 1), (8731213, 1), (2686553917, 1), (12383928439, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_97, prime_oneHundredFortyThreeEK_8731213, prime_oneHundredFortyThreeEK_2686553917, prime_oneHundredFortyThreeEK_12383928439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708859 : Nat.totient 169064164426703607134124708859 = 168894853734727720103182068096 := by
  rw [← show ((([(1009, 1), (96263, 1), (1740608115223314562877, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_1009, prime_oneHundredFortyThreeEK_96263, prime_oneHundredFortyThreeEK_1740608115223314562877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708860 : Nat.totient 169064164426703607134124708860 = 56398238631757492811575849728 := by
  rw [← show ((([(2, 2), (5, 1), (7, 1), (37, 1), (17348290783, 1), (1881330558075919, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_37, prime_oneHundredFortyThreeEK_17348290783, prime_oneHundredFortyThreeEK_1881330558075919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708861 : Nat.totient 169064164426703607134124708861 = 102778490493896848828491571200 := by
  rw [← show ((([(3, 2), (19, 2), (31, 1), (331, 1), (719, 1), (1109, 1), (25229, 1), (48527, 1), (5194793, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_19, prime_oneHundredFortyThreeEK_31, prime_oneHundredFortyThreeEK_331, prime_oneHundredFortyThreeEK_719, prime_oneHundredFortyThreeEK_1109, prime_oneHundredFortyThreeEK_25229, prime_oneHundredFortyThreeEK_48527, prime_oneHundredFortyThreeEK_5194793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708862 : Nat.totient 169064164426703607134124708862 = 83513623391504191475892928392 := by
  rw [← show ((([(2, 1), (83, 1), (1018458821847612091169425957, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_83, prime_oneHundredFortyThreeEK_1018458821847612091169425957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708863 : Nat.totient 169064164426703607134124708863 = 168871619417104480181377831704 := by
  rw [← show ((([(887, 1), (86923, 1), (2192770782028345074763, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_887, prime_oneHundredFortyThreeEK_86923, prime_oneHundredFortyThreeEK_2192770782028345074763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708864 : Nat.totient 169064164426703607134124708864 = 56194839373909614201544900608 := by
  rw [← show ((([(2, 10), (3, 1), (353, 1), (251893, 1), (4040789, 1), (153169880527, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_353, prime_oneHundredFortyThreeEK_251893, prime_oneHundredFortyThreeEK_4040789, prime_oneHundredFortyThreeEK_153169880527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708865 : Nat.totient 169064164426703607134124708865 = 117487939950678259789311513600 := by
  rw [← show ((([(5, 1), (13, 2), (17, 1), (7591, 1), (1550411355806685423811, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_13, prime_oneHundredFortyThreeEK_17, prime_oneHundredFortyThreeEK_7591, prime_oneHundredFortyThreeEK_1550411355806685423811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708866 : Nat.totient 169064164426703607134124708866 = 76597021148071289065597553040 := by
  rw [← show ((([(2, 1), (11, 1), (307, 1), (8302403, 1), (3014995691311940443, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_11, prime_oneHundredFortyThreeEK_307, prime_oneHundredFortyThreeEK_8302403, prime_oneHundredFortyThreeEK_3014995691311940443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708867 : Nat.totient 169064164426703607134124708867 = 95651757919741542498733925376 := by
  rw [← show ((([(3, 1), (7, 1), (109, 1), (1367, 1), (142197159337, 1), (379967397757, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_109, prime_oneHundredFortyThreeEK_1367, prime_oneHundredFortyThreeEK_142197159337, prime_oneHundredFortyThreeEK_379967397757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708868 : Nat.totient 169064164426703607134124708868 = 84532082213351803567062354432 := by
  rw [← show ((([(2, 2), (42266041106675901783531177217, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_42266041106675901783531177217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708869 : Nat.totient 169064164426703607134124708869 = 168478166933193990444614025984 := by
  rw [← show ((([(337, 1), (1999, 1), (20544302087, 1), (12215675149549, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_337, prime_oneHundredFortyThreeEK_1999, prime_oneHundredFortyThreeEK_20544302087, prime_oneHundredFortyThreeEK_12215675149549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708870 : Nat.totient 169064164426703607134124708870 = 45072810558504556593994874880 := by
  rw [← show ((([(2, 1), (3, 5), (5, 1), (4111, 1), (35160493427, 1), (481329911297, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_4111, prime_oneHundredFortyThreeEK_35160493427, prime_oneHundredFortyThreeEK_481329911297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708871 : Nat.totient 169064164426703607134124708871 = 169064164423664715144905534200 := by
  rw [← show ((([(55633490141, 1), (3038891933585684531, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_55633490141, prime_oneHundredFortyThreeEK_3038891933585684531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708872 : Nat.totient 169064164426703607134124708872 = 84070408784651661746855416320 := by
  rw [← show ((([(2, 3), (199, 1), (2281, 1), (5220923, 1), (8917352317325357, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_199, prime_oneHundredFortyThreeEK_2281, prime_oneHundredFortyThreeEK_5220923, prime_oneHundredFortyThreeEK_8917352317325357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708873 : Nat.totient 169064164426703607134124708873 = 112709442951135738089416472580 := by
  rw [← show ((([(3, 1), (56354721475567869044708236291, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_56354721475567869044708236291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708874 : Nat.totient 169064164426703607134124708874 = 72456070451357806307554113792 := by
  rw [← show ((([(2, 1), (7, 1), (4205360833, 1), (2871575644592147027, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_4205360833, prime_oneHundredFortyThreeEK_2871575644592147027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708875 : Nat.totient 169064164426703607134124708875 = 134874832191101778416344704000 := by
  rw [← show ((([(5, 3), (827, 1), (859, 1), (3769, 1), (6781, 1), (74494291529123, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_827, prime_oneHundredFortyThreeEK_859, prime_oneHundredFortyThreeEK_3769, prime_oneHundredFortyThreeEK_6781, prime_oneHundredFortyThreeEK_74494291529123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708876 : Nat.totient 169064164426703607134124708876 = 53644539764339779182301194240 := by
  rw [← show ((([(2, 2), (3, 1), (29, 1), (71, 1), (96323, 1), (71036894855462189089, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_29, prime_oneHundredFortyThreeEK_71, prime_oneHundredFortyThreeEK_96323, prime_oneHundredFortyThreeEK_71036894855462189089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708877 : Nat.totient 169064164426703607134124708877 = 144237296893828291966621585920 := by
  rw [← show ((([(11, 1), (23, 1), (53, 1), (119929, 1), (105131039647847779157, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_11, prime_oneHundredFortyThreeEK_23, prime_oneHundredFortyThreeEK_53, prime_oneHundredFortyThreeEK_119929, prime_oneHundredFortyThreeEK_105131039647847779157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708878 : Nat.totient 169064164426703607134124708878 = 78029614350786280215749865624 := by
  rw [← show ((([(2, 1), (13, 1), (6502467862565523351312488803, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_13, prime_oneHundredFortyThreeEK_6502467862565523351312488803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708879 : Nat.totient 169064164426703607134124708879 = 112590425232609018778847174400 := by
  rw [← show ((([(3, 2), (947, 1), (316865201, 1), (62601469449873373, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_947, prime_oneHundredFortyThreeEK_316865201, prime_oneHundredFortyThreeEK_62601469449873373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708880 : Nat.totient 169064164426703607134124708880 = 62429491318293398713130680320 := by
  rw [← show ((([(2, 4), (5, 1), (19, 1), (47, 1), (229, 1), (17901381821, 1), (577282082753, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_19, prime_oneHundredFortyThreeEK_47, prime_oneHundredFortyThreeEK_229, prime_oneHundredFortyThreeEK_17901381821, prime_oneHundredFortyThreeEK_577282082753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708881 : Nat.totient 169064164426703607134124708881 = 144896839946014731650023525200 := by
  rw [← show ((([(7, 1), (11423, 1), (55411, 1), (38157275497106586211, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_11423, prime_oneHundredFortyThreeEK_55411, prime_oneHundredFortyThreeEK_38157275497106586211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708882 : Nat.totient 169064164426703607134124708882 = 52514591939958410292098476800 := by
  rw [← show ((([(2, 1), (3, 1), (17, 2), (101, 1), (965341763602176659781223, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_17, prime_oneHundredFortyThreeEK_101, prime_oneHundredFortyThreeEK_965341763602176659781223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708883 : Nat.totient 169064164426703607134124708883 = 169064164426703607134124708882 := by
  rw [← show ((([(169064164426703607134124708883, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_169064164426703607134124708883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708884 : Nat.totient 169064164426703607134124708884 = 84351070810580887468012179456 := by
  rw [← show ((([(2, 2), (467, 1), (162186439, 1), (558033346683926017, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_467, prime_oneHundredFortyThreeEK_162186439, prime_oneHundredFortyThreeEK_558033346683926017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708885 : Nat.totient 169064164426703607134124708885 = 90167554356795570830607535680 := by
  rw [← show ((([(3, 1), (5, 1), (21922472071, 1), (514127433193233229, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_21922472071, prime_oneHundredFortyThreeEK_514127433193233229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708886 : Nat.totient 169064164426703607134124708886 = 84229013468773044224908498944 := by
  rw [← show ((([(2, 1), (283, 1), (20479, 1), (329473, 1), (44269697545948463, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_283, prime_oneHundredFortyThreeEK_20479, prime_oneHundredFortyThreeEK_329473, prime_oneHundredFortyThreeEK_44269697545948463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708887 : Nat.totient 169064164426703607134124708887 = 169064164043818683702727575672 := by
  rw [← show ((([(577198243, 1), (1902115487, 1), (153988993507, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_577198243, prime_oneHundredFortyThreeEK_1902115487, prime_oneHundredFortyThreeEK_153988993507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708888 : Nat.totient 169064164426703607134124708888 = 43906710539816541633594188160 := by
  rw [← show ((([(2, 3), (3, 2), (7, 2), (11, 1), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_11, prime_oneHundredFortyThreeEK_7247, prime_oneHundredFortyThreeEK_601135034269270369663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708889 : Nat.totient 169064164426703607134124708889 = 166172875963524732438804818304 := by
  rw [← show ((([(59, 1), (6469, 1), (1619687, 1), (273483609494575657, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_59, prime_oneHundredFortyThreeEK_6469, prime_oneHundredFortyThreeEK_1619687, prime_oneHundredFortyThreeEK_273483609494575657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708890 : Nat.totient 169064164426703607134124708890 = 65976259287849246536602877440 := by
  rw [← show ((([(2, 1), (5, 1), (41, 1), (106338405293, 1), (3877729964228453, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_41, prime_oneHundredFortyThreeEK_106338405293, prime_oneHundredFortyThreeEK_3877729964228453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708891 : Nat.totient 169064164426703607134124708891 = 102722528208178040987643122304 := by
  rw [← show ((([(3, 1), (13, 1), (79, 1), (49471423, 1), (1109188763774599357, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_13, prime_oneHundredFortyThreeEK_79, prime_oneHundredFortyThreeEK_49471423, prime_oneHundredFortyThreeEK_1109188763774599357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708892 : Nat.totient 169064164426703607134124708892 = 81805170039725746400401208880 := by
  rw [← show ((([(2, 2), (31, 1), (1155247, 1), (1180198417187417894839, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_31, prime_oneHundredFortyThreeEK_1155247, prime_oneHundredFortyThreeEK_1180198417187417894839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708893 : Nat.totient 169064164426703607134124708893 = 169064160483325067860064034400 := by
  rw [← show ((([(48347207, 1), (378656099, 1), (9234964193801, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_48347207, prime_oneHundredFortyThreeEK_378656099, prime_oneHundredFortyThreeEK_9234964193801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708894 : Nat.totient 169064164426703607134124708894 = 55044146557456630893208202880 := by
  rw [← show ((([(2, 1), (3, 1), (43, 1), (736729429361, 1), (889454707390463, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_43, prime_oneHundredFortyThreeEK_736729429361, prime_oneHundredFortyThreeEK_889454707390463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708895 : Nat.totient 169064164426703607134124708895 = 115384894727558621678690411520 := by
  rw [← show ((([(5, 1), (7, 1), (359, 1), (521, 1), (42466287607, 1), (608144872589, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_7, prime_oneHundredFortyThreeEK_359, prime_oneHundredFortyThreeEK_521, prime_oneHundredFortyThreeEK_42466287607, prime_oneHundredFortyThreeEK_608144872589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708896 : Nat.totient 169064164426703607134124708896 = 84532082212692082858863124800 := by
  rw [← show ((([(2, 5), (128133532651, 1), (41232416128919203, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_128133532651, prime_oneHundredFortyThreeEK_41232416128919203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708897 : Nat.totient 169064164426703607134124708897 = 108161005601386091494915724160 := by
  rw [← show ((([(3, 3), (37, 1), (73, 1), (2318265723623673085882111, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_37, prime_oneHundredFortyThreeEK_73, prime_oneHundredFortyThreeEK_2318265723623673085882111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708898 : Nat.totient 169064164426703607134124708898 = 84498535419985762245418558464 := by
  rw [← show ((([(2, 1), (3209, 1), (20089, 1), (32869, 1), (197807, 1), (201681184403, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3209, prime_oneHundredFortyThreeEK_20089, prime_oneHundredFortyThreeEK_32869, prime_oneHundredFortyThreeEK_197807, prime_oneHundredFortyThreeEK_201681184403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708899 : Nat.totient 169064164426703607134124708899 = 136121637264124426750869350400 := by
  rw [← show ((([(11, 1), (17, 1), (19, 1), (163, 1), (1759, 1), (204859, 1), (810117218002061, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_11, prime_oneHundredFortyThreeEK_17, prime_oneHundredFortyThreeEK_19, prime_oneHundredFortyThreeEK_163, prime_oneHundredFortyThreeEK_1759, prime_oneHundredFortyThreeEK_204859, prime_oneHundredFortyThreeEK_810117218002061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708900 : Nat.totient 169064164426703607134124708900 = 43123612920372416214723008640 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (23, 1), (1237593419, 1), (19798144074862999, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_2, prime_oneHundredFortyThreeEK_3, prime_oneHundredFortyThreeEK_5, prime_oneHundredFortyThreeEK_23, prime_oneHundredFortyThreeEK_1237593419, prime_oneHundredFortyThreeEK_19798144074862999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyThreeEK_169064164426703607134124708901 : Nat.totient 169064164426703607134124708901 = 169055060977898972386395798528 := by
  rw [← show ((([(18679, 1), (3660913, 1), (27092657, 1), (91255055459, 1)] : List FactorBlock).map factorBlockValue).prod) = 169064164426703607134124708901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyThreeEK_18679, prime_oneHundredFortyThreeEK_3660913, prime_oneHundredFortyThreeEK_27092657, prime_oneHundredFortyThreeEK_91255055459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFortyThreeEK : certifiedKill 1 169064164426703607134124708799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFortyThreeEK_169064164426703607134124708800, phi_oneHundredFortyThreeEK_169064164426703607134124708801, phi_oneHundredFortyThreeEK_169064164426703607134124708802,
    phi_oneHundredFortyThreeEK_169064164426703607134124708803, phi_oneHundredFortyThreeEK_169064164426703607134124708804, phi_oneHundredFortyThreeEK_169064164426703607134124708805,
    phi_oneHundredFortyThreeEK_169064164426703607134124708806, phi_oneHundredFortyThreeEK_169064164426703607134124708807, phi_oneHundredFortyThreeEK_169064164426703607134124708808,
    phi_oneHundredFortyThreeEK_169064164426703607134124708809, phi_oneHundredFortyThreeEK_169064164426703607134124708810, phi_oneHundredFortyThreeEK_169064164426703607134124708811,
    phi_oneHundredFortyThreeEK_169064164426703607134124708812, phi_oneHundredFortyThreeEK_169064164426703607134124708813, phi_oneHundredFortyThreeEK_169064164426703607134124708814,
    phi_oneHundredFortyThreeEK_169064164426703607134124708815, phi_oneHundredFortyThreeEK_169064164426703607134124708816, phi_oneHundredFortyThreeEK_169064164426703607134124708817,
    phi_oneHundredFortyThreeEK_169064164426703607134124708818, phi_oneHundredFortyThreeEK_169064164426703607134124708819, phi_oneHundredFortyThreeEK_169064164426703607134124708820,
    phi_oneHundredFortyThreeEK_169064164426703607134124708821, phi_oneHundredFortyThreeEK_169064164426703607134124708822, phi_oneHundredFortyThreeEK_169064164426703607134124708823,
    phi_oneHundredFortyThreeEK_169064164426703607134124708824, phi_oneHundredFortyThreeEK_169064164426703607134124708825, phi_oneHundredFortyThreeEK_169064164426703607134124708826,
    phi_oneHundredFortyThreeEK_169064164426703607134124708827, phi_oneHundredFortyThreeEK_169064164426703607134124708828, phi_oneHundredFortyThreeEK_169064164426703607134124708829,
    phi_oneHundredFortyThreeEK_169064164426703607134124708830, phi_oneHundredFortyThreeEK_169064164426703607134124708831, phi_oneHundredFortyThreeEK_169064164426703607134124708832,
    phi_oneHundredFortyThreeEK_169064164426703607134124708833, phi_oneHundredFortyThreeEK_169064164426703607134124708834, phi_oneHundredFortyThreeEK_169064164426703607134124708835,
    phi_oneHundredFortyThreeEK_169064164426703607134124708836, phi_oneHundredFortyThreeEK_169064164426703607134124708837, phi_oneHundredFortyThreeEK_169064164426703607134124708838,
    phi_oneHundredFortyThreeEK_169064164426703607134124708839, phi_oneHundredFortyThreeEK_169064164426703607134124708840, phi_oneHundredFortyThreeEK_169064164426703607134124708841,
    phi_oneHundredFortyThreeEK_169064164426703607134124708842, phi_oneHundredFortyThreeEK_169064164426703607134124708843, phi_oneHundredFortyThreeEK_169064164426703607134124708844,
    phi_oneHundredFortyThreeEK_169064164426703607134124708845, phi_oneHundredFortyThreeEK_169064164426703607134124708846, phi_oneHundredFortyThreeEK_169064164426703607134124708847,
    phi_oneHundredFortyThreeEK_169064164426703607134124708848, phi_oneHundredFortyThreeEK_169064164426703607134124708849, phi_oneHundredFortyThreeEK_169064164426703607134124708850,
    phi_oneHundredFortyThreeEK_169064164426703607134124708851, phi_oneHundredFortyThreeEK_169064164426703607134124708852, phi_oneHundredFortyThreeEK_169064164426703607134124708853,
    phi_oneHundredFortyThreeEK_169064164426703607134124708854, phi_oneHundredFortyThreeEK_169064164426703607134124708855, phi_oneHundredFortyThreeEK_169064164426703607134124708856,
    phi_oneHundredFortyThreeEK_169064164426703607134124708857, phi_oneHundredFortyThreeEK_169064164426703607134124708858, phi_oneHundredFortyThreeEK_169064164426703607134124708859,
    phi_oneHundredFortyThreeEK_169064164426703607134124708860, phi_oneHundredFortyThreeEK_169064164426703607134124708861, phi_oneHundredFortyThreeEK_169064164426703607134124708862,
    phi_oneHundredFortyThreeEK_169064164426703607134124708863, phi_oneHundredFortyThreeEK_169064164426703607134124708864, phi_oneHundredFortyThreeEK_169064164426703607134124708865,
    phi_oneHundredFortyThreeEK_169064164426703607134124708866, phi_oneHundredFortyThreeEK_169064164426703607134124708867, phi_oneHundredFortyThreeEK_169064164426703607134124708868,
    phi_oneHundredFortyThreeEK_169064164426703607134124708869, phi_oneHundredFortyThreeEK_169064164426703607134124708870, phi_oneHundredFortyThreeEK_169064164426703607134124708871,
    phi_oneHundredFortyThreeEK_169064164426703607134124708872, phi_oneHundredFortyThreeEK_169064164426703607134124708873, phi_oneHundredFortyThreeEK_169064164426703607134124708874,
    phi_oneHundredFortyThreeEK_169064164426703607134124708875, phi_oneHundredFortyThreeEK_169064164426703607134124708876, phi_oneHundredFortyThreeEK_169064164426703607134124708877,
    phi_oneHundredFortyThreeEK_169064164426703607134124708878, phi_oneHundredFortyThreeEK_169064164426703607134124708879, phi_oneHundredFortyThreeEK_169064164426703607134124708880,
    phi_oneHundredFortyThreeEK_169064164426703607134124708881, phi_oneHundredFortyThreeEK_169064164426703607134124708882, phi_oneHundredFortyThreeEK_169064164426703607134124708883,
    phi_oneHundredFortyThreeEK_169064164426703607134124708884, phi_oneHundredFortyThreeEK_169064164426703607134124708885, phi_oneHundredFortyThreeEK_169064164426703607134124708886,
    phi_oneHundredFortyThreeEK_169064164426703607134124708887, phi_oneHundredFortyThreeEK_169064164426703607134124708888, phi_oneHundredFortyThreeEK_169064164426703607134124708889,
    phi_oneHundredFortyThreeEK_169064164426703607134124708890, phi_oneHundredFortyThreeEK_169064164426703607134124708891, phi_oneHundredFortyThreeEK_169064164426703607134124708892,
    phi_oneHundredFortyThreeEK_169064164426703607134124708893, phi_oneHundredFortyThreeEK_169064164426703607134124708894, phi_oneHundredFortyThreeEK_169064164426703607134124708895,
    phi_oneHundredFortyThreeEK_169064164426703607134124708896, phi_oneHundredFortyThreeEK_169064164426703607134124708897, phi_oneHundredFortyThreeEK_169064164426703607134124708898,
    phi_oneHundredFortyThreeEK_169064164426703607134124708899, phi_oneHundredFortyThreeEK_169064164426703607134124708900, phi_oneHundredFortyThreeEK_169064164426703607134124708901]

end TotientTailPeriodKiller
end Erdos249257
