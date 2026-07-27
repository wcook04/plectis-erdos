import Erdos249257.DiagonalPincerCertificatesT64
/- Kernel-checked off-diagonal certificate at a freely chosen position. -/
namespace Erdos249257
namespace TotientTailPeriodKiller
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private def oneHundredFortyNineEQFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFortyNineEQFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFortyNineEQFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFortyNineEQFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFortyNineEQFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFortyNineEQFastPow a n * oneHundredFortyNineEQFastPow a n * a else oneHundredFortyNineEQFastPow a n * oneHundredFortyNineEQFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFortyNineEQ_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFortyNineEQ_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFortyNineEQ_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFortyNineEQ_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFortyNineEQ_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFortyNineEQ_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFortyNineEQ_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFortyNineEQ_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFortyNineEQ_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFortyNineEQ_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFortyNineEQ_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFortyNineEQ_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFortyNineEQ_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFortyNineEQ_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFortyNineEQ_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFortyNineEQ_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFortyNineEQ_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFortyNineEQ_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFortyNineEQ_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFortyNineEQ_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFortyNineEQ_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFortyNineEQ_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFortyNineEQ_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFortyNineEQ_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFortyNineEQ_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFortyNineEQ_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFortyNineEQ_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFortyNineEQ_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFortyNineEQ_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFortyNineEQ_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFortyNineEQ_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFortyNineEQ_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFortyNineEQ_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFortyNineEQ_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFortyNineEQ_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFortyNineEQ_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFortyNineEQ_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFortyNineEQ_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFortyNineEQ_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFortyNineEQ_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFortyNineEQ_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFortyNineEQ_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFortyNineEQ_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFortyNineEQ_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredFortyNineEQ_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFortyNineEQ_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFortyNineEQ_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFortyNineEQ_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFortyNineEQ_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFortyNineEQ_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFortyNineEQ_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFortyNineEQ_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFortyNineEQ_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFortyNineEQ_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFortyNineEQ_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFortyNineEQ_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFortyNineEQ_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredFortyNineEQ_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFortyNineEQ_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFortyNineEQ_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredFortyNineEQ_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFortyNineEQ_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredFortyNineEQ_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredFortyNineEQ_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredFortyNineEQ_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFortyNineEQ_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredFortyNineEQ_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredFortyNineEQ_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredFortyNineEQ_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredFortyNineEQ_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredFortyNineEQ_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredFortyNineEQ_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredFortyNineEQ_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFortyNineEQ_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredFortyNineEQ_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredFortyNineEQ_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredFortyNineEQ_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredFortyNineEQ_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredFortyNineEQ_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredFortyNineEQ_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredFortyNineEQ_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredFortyNineEQ_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredFortyNineEQ_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredFortyNineEQ_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredFortyNineEQ_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredFortyNineEQ_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredFortyNineEQ_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredFortyNineEQ_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredFortyNineEQ_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredFortyNineEQ_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredFortyNineEQ_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredFortyNineEQ_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1777 : Nat.Prime 1777 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1999 : Nat.Prime 1999 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2341 : Nat.Prime 2341 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2539 : Nat.Prime 2539 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2683 : Nat.Prime 2683 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2749 : Nat.Prime 2749 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2837 : Nat.Prime 2837 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3407 : Nat.Prime 3407 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3581 : Nat.Prime 3581 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3697 : Nat.Prime 3697 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4139 : Nat.Prime 4139 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4813 : Nat.Prime 4813 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4903 : Nat.Prime 4903 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4931 : Nat.Prime 4931 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4933 : Nat.Prime 4933 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5099 : Nat.Prime 5099 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5113 : Nat.Prime 5113 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5119 : Nat.Prime 5119 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5273 : Nat.Prime 5273 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5399 : Nat.Prime 5399 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5419 : Nat.Prime 5419 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5443 : Nat.Prime 5443 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5519 : Nat.Prime 5519 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5689 : Nat.Prime 5689 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5693 : Nat.Prime 5693 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5737 : Nat.Prime 5737 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5867 : Nat.Prime 5867 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5881 : Nat.Prime 5881 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5923 : Nat.Prime 5923 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5987 : Nat.Prime 5987 := by norm_num

private theorem prime_oneHundredFortyNineEQ_6053 : Nat.Prime 6053 := by norm_num

private theorem prime_oneHundredFortyNineEQ_6269 : Nat.Prime 6269 := by norm_num

private theorem prime_oneHundredFortyNineEQ_6277 : Nat.Prime 6277 := by norm_num

private theorem prime_oneHundredFortyNineEQ_6871 : Nat.Prime 6871 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7043 : Nat.Prime 7043 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7103 : Nat.Prime 7103 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7109 : Nat.Prime 7109 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7331 : Nat.Prime 7331 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7369 : Nat.Prime 7369 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7451 : Nat.Prime 7451 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7489 : Nat.Prime 7489 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7537 : Nat.Prime 7537 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7951 : Nat.Prime 7951 := by norm_num

private theorem prime_oneHundredFortyNineEQ_8089 : Nat.Prime 8089 := by norm_num

private theorem prime_oneHundredFortyNineEQ_8209 : Nat.Prime 8209 := by norm_num

private theorem prime_oneHundredFortyNineEQ_8629 : Nat.Prime 8629 := by norm_num

private theorem prime_oneHundredFortyNineEQ_8641 : Nat.Prime 8641 := by norm_num

private theorem prime_oneHundredFortyNineEQ_8887 : Nat.Prime 8887 := by norm_num

private theorem prime_oneHundredFortyNineEQ_8941 : Nat.Prime 8941 := by norm_num

private theorem prime_oneHundredFortyNineEQ_8951 : Nat.Prime 8951 := by norm_num

private theorem prime_oneHundredFortyNineEQ_9091 : Nat.Prime 9091 := by norm_num

private theorem prime_oneHundredFortyNineEQ_9199 : Nat.Prime 9199 := by norm_num

private theorem prime_oneHundredFortyNineEQ_9463 : Nat.Prime 9463 := by norm_num

private theorem prime_oneHundredFortyNineEQ_9533 : Nat.Prime 9533 := by norm_num

private theorem prime_oneHundredFortyNineEQ_9743 : Nat.Prime 9743 := by norm_num

private theorem prime_oneHundredFortyNineEQ_9749 : Nat.Prime 9749 := by norm_num

private theorem prime_oneHundredFortyNineEQ_9829 : Nat.Prime 9829 := by norm_num

private theorem prime_oneHundredFortyNineEQ_9901 : Nat.Prime 9901 := by norm_num

private theorem prime_oneHundredFortyNineEQ_10039 : Nat.Prime 10039 := by norm_num

private theorem prime_oneHundredFortyNineEQ_10273 : Nat.Prime 10273 := by norm_num

private theorem prime_oneHundredFortyNineEQ_10303 : Nat.Prime 10303 := by norm_num

private theorem prime_oneHundredFortyNineEQ_10651 : Nat.Prime 10651 := by norm_num

private theorem prime_oneHundredFortyNineEQ_10691 : Nat.Prime 10691 := by norm_num

private theorem prime_oneHundredFortyNineEQ_10831 : Nat.Prime 10831 := by norm_num

private theorem prime_oneHundredFortyNineEQ_10909 : Nat.Prime 10909 := by norm_num

private theorem prime_oneHundredFortyNineEQ_11393 : Nat.Prime 11393 := by norm_num

private theorem prime_oneHundredFortyNineEQ_11491 : Nat.Prime 11491 := by norm_num

private theorem prime_oneHundredFortyNineEQ_11519 : Nat.Prime 11519 := by norm_num

private theorem prime_oneHundredFortyNineEQ_11971 : Nat.Prime 11971 := by norm_num

private theorem prime_oneHundredFortyNineEQ_12457 : Nat.Prime 12457 := by norm_num

private theorem prime_oneHundredFortyNineEQ_13127 : Nat.Prime 13127 := by norm_num

private theorem prime_oneHundredFortyNineEQ_13313 : Nat.Prime 13313 := by norm_num

private theorem prime_oneHundredFortyNineEQ_13421 : Nat.Prime 13421 := by norm_num

private theorem prime_oneHundredFortyNineEQ_14401 : Nat.Prime 14401 := by norm_num

private theorem prime_oneHundredFortyNineEQ_14519 : Nat.Prime 14519 := by norm_num

private theorem prime_oneHundredFortyNineEQ_14731 : Nat.Prime 14731 := by norm_num

private theorem prime_oneHundredFortyNineEQ_15107 : Nat.Prime 15107 := by norm_num

private theorem prime_oneHundredFortyNineEQ_15307 : Nat.Prime 15307 := by norm_num

private theorem prime_oneHundredFortyNineEQ_15391 : Nat.Prime 15391 := by norm_num

private theorem prime_oneHundredFortyNineEQ_16931 : Nat.Prime 16931 := by norm_num

private theorem prime_oneHundredFortyNineEQ_16963 : Nat.Prime 16963 := by norm_num

private theorem prime_oneHundredFortyNineEQ_17167 : Nat.Prime 17167 := by norm_num

private theorem prime_oneHundredFortyNineEQ_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFortyNineEQ_17299 : Nat.Prime 17299 := by norm_num

private theorem prime_oneHundredFortyNineEQ_17471 : Nat.Prime 17471 := by norm_num

private theorem prime_oneHundredFortyNineEQ_19577 : Nat.Prime 19577 := by norm_num

private theorem prime_oneHundredFortyNineEQ_20249 : Nat.Prime 20249 := by norm_num

private theorem prime_oneHundredFortyNineEQ_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFortyNineEQ_21323 : Nat.Prime 21323 := by norm_num

private theorem prime_oneHundredFortyNineEQ_21347 : Nat.Prime 21347 := by norm_num

private theorem prime_oneHundredFortyNineEQ_22369 : Nat.Prime 22369 := by norm_num

private theorem prime_oneHundredFortyNineEQ_22699 : Nat.Prime 22699 := by norm_num

private theorem prime_oneHundredFortyNineEQ_22727 : Nat.Prime 22727 := by norm_num

private theorem prime_oneHundredFortyNineEQ_22937 : Nat.Prime 22937 := by norm_num

private theorem prime_oneHundredFortyNineEQ_23321 : Nat.Prime 23321 := by norm_num

private theorem prime_oneHundredFortyNineEQ_23909 : Nat.Prime 23909 := by norm_num

private theorem prime_oneHundredFortyNineEQ_24001 : Nat.Prime 24001 := by norm_num

private theorem prime_oneHundredFortyNineEQ_25307 : Nat.Prime 25307 := by norm_num

private theorem prime_oneHundredFortyNineEQ_29059 : Nat.Prime 29059 := by norm_num

private theorem prime_oneHundredFortyNineEQ_29123 : Nat.Prime 29123 := by norm_num

private theorem prime_oneHundredFortyNineEQ_30449 : Nat.Prime 30449 := by norm_num

private theorem prime_oneHundredFortyNineEQ_30841 : Nat.Prime 30841 := by norm_num

private theorem prime_oneHundredFortyNineEQ_32443 : Nat.Prime 32443 := by norm_num

private theorem prime_oneHundredFortyNineEQ_33479 : Nat.Prime 33479 := by norm_num

private theorem prime_oneHundredFortyNineEQ_34253 : Nat.Prime 34253 := by norm_num

private theorem prime_oneHundredFortyNineEQ_34651 : Nat.Prime 34651 := by norm_num

private theorem prime_oneHundredFortyNineEQ_35051 : Nat.Prime 35051 := by norm_num

private theorem prime_oneHundredFortyNineEQ_35059 : Nat.Prime 35059 := by norm_num

private theorem prime_oneHundredFortyNineEQ_35507 : Nat.Prime 35507 := by norm_num

private theorem prime_oneHundredFortyNineEQ_36037 : Nat.Prime 36037 := by norm_num

private theorem prime_oneHundredFortyNineEQ_36451 : Nat.Prime 36451 := by norm_num

private theorem prime_oneHundredFortyNineEQ_38219 : Nat.Prime 38219 := by norm_num

private theorem prime_oneHundredFortyNineEQ_39161 : Nat.Prime 39161 := by norm_num

private theorem prime_oneHundredFortyNineEQ_45247 : Nat.Prime 45247 := by norm_num

private theorem prime_oneHundredFortyNineEQ_47129 : Nat.Prime 47129 := by norm_num

private theorem prime_oneHundredFortyNineEQ_49991 : Nat.Prime 49991 := by norm_num

private theorem prime_oneHundredFortyNineEQ_52067 : Nat.Prime 52067 := by norm_num

private theorem prime_oneHundredFortyNineEQ_52163 : Nat.Prime 52163 := by norm_num

private theorem prime_oneHundredFortyNineEQ_52721 : Nat.Prime 52721 := by norm_num

private theorem prime_oneHundredFortyNineEQ_53887 : Nat.Prime 53887 := by norm_num

private theorem prime_oneHundredFortyNineEQ_54577 : Nat.Prime 54577 := by norm_num

private theorem prime_oneHundredFortyNineEQ_55079 : Nat.Prime 55079 := by norm_num

private theorem prime_oneHundredFortyNineEQ_56041 : Nat.Prime 56041 := by norm_num

private theorem prime_oneHundredFortyNineEQ_56713 : Nat.Prime 56713 := by norm_num

private theorem prime_oneHundredFortyNineEQ_58199 : Nat.Prime 58199 := by norm_num

private theorem prime_oneHundredFortyNineEQ_59513 : Nat.Prime 59513 := by norm_num

private theorem prime_oneHundredFortyNineEQ_59779 : Nat.Prime 59779 := by norm_num

private theorem prime_oneHundredFortyNineEQ_62189 : Nat.Prime 62189 := by norm_num

private theorem prime_oneHundredFortyNineEQ_63103 : Nat.Prime 63103 := by norm_num

private theorem prime_oneHundredFortyNineEQ_66071 : Nat.Prime 66071 := by norm_num

private theorem prime_oneHundredFortyNineEQ_66457 : Nat.Prime 66457 := by norm_num

private theorem prime_oneHundredFortyNineEQ_66733 : Nat.Prime 66733 := by norm_num

private theorem prime_oneHundredFortyNineEQ_69401 : Nat.Prime 69401 := by norm_num

private theorem prime_oneHundredFortyNineEQ_69767 : Nat.Prime 69767 := by norm_num

private theorem prime_oneHundredFortyNineEQ_69859 : Nat.Prime 69859 := by norm_num

private theorem prime_oneHundredFortyNineEQ_75853 : Nat.Prime 75853 := by norm_num

private theorem prime_oneHundredFortyNineEQ_77969 : Nat.Prime 77969 := by norm_num

private theorem prime_oneHundredFortyNineEQ_79841 : Nat.Prime 79841 := by norm_num

private theorem prime_oneHundredFortyNineEQ_80231 : Nat.Prime 80231 := by norm_num

private theorem prime_oneHundredFortyNineEQ_80669 : Nat.Prime 80669 := by norm_num

private theorem prime_oneHundredFortyNineEQ_83621 : Nat.Prime 83621 := by norm_num

private theorem prime_oneHundredFortyNineEQ_85601 : Nat.Prime 85601 := by norm_num

private theorem prime_oneHundredFortyNineEQ_86293 : Nat.Prime 86293 := by norm_num

private theorem prime_oneHundredFortyNineEQ_90059 : Nat.Prime 90059 := by norm_num

private theorem prime_oneHundredFortyNineEQ_91691 : Nat.Prime 91691 := by norm_num

private theorem prime_oneHundredFortyNineEQ_92557 : Nat.Prime 92557 := by norm_num

private theorem prime_oneHundredFortyNineEQ_93241 : Nat.Prime 93241 := by norm_num

private theorem prime_oneHundredFortyNineEQ_94781 : Nat.Prime 94781 := by norm_num

private theorem prime_oneHundredFortyNineEQ_96013 : Nat.Prime 96013 := by norm_num

private theorem prime_oneHundredFortyNineEQ_98837 : Nat.Prime 98837 := by norm_num

private theorem prime_oneHundredFortyNineEQ_99713 : Nat.Prime 99713 := by norm_num

private theorem prime_oneHundredFortyNineEQ_103319 : Nat.Prime 103319 := by norm_num

private theorem prime_oneHundredFortyNineEQ_103811 : Nat.Prime 103811 := by norm_num

private theorem prime_oneHundredFortyNineEQ_106433 : Nat.Prime 106433 := by norm_num

private theorem prime_oneHundredFortyNineEQ_134059 : Nat.Prime 134059 := by norm_num

private theorem prime_oneHundredFortyNineEQ_157049 : Nat.Prime 157049 := by norm_num

private theorem prime_oneHundredFortyNineEQ_164743 : Nat.Prime 164743 := by norm_num

private theorem prime_oneHundredFortyNineEQ_169313 : Nat.Prime 169313 := by norm_num

private theorem prime_oneHundredFortyNineEQ_169991 : Nat.Prime 169991 := by norm_num

private theorem prime_oneHundredFortyNineEQ_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFortyNineEQ_187273 : Nat.Prime 187273 := by norm_num

private theorem prime_oneHundredFortyNineEQ_191353 : Nat.Prime 191353 := by norm_num

private theorem prime_oneHundredFortyNineEQ_192037 : Nat.Prime 192037 := by norm_num

private theorem prime_oneHundredFortyNineEQ_193493 : Nat.Prime 193493 := by norm_num

private theorem prime_oneHundredFortyNineEQ_197137 : Nat.Prime 197137 := by norm_num

private theorem prime_oneHundredFortyNineEQ_198463 : Nat.Prime 198463 := by norm_num

private theorem prime_oneHundredFortyNineEQ_198479 : Nat.Prime 198479 := by norm_num

private theorem prime_oneHundredFortyNineEQ_202403 : Nat.Prime 202403 := by norm_num

private theorem prime_oneHundredFortyNineEQ_224771 : Nat.Prime 224771 := by norm_num

private theorem prime_oneHundredFortyNineEQ_228409 : Nat.Prime 228409 := by norm_num

private theorem prime_oneHundredFortyNineEQ_240203 : Nat.Prime 240203 := by norm_num

private theorem prime_oneHundredFortyNineEQ_248257 : Nat.Prime 248257 := by norm_num

private theorem prime_oneHundredFortyNineEQ_306913 : Nat.Prime 306913 := by norm_num

private theorem prime_oneHundredFortyNineEQ_311743 : Nat.Prime 311743 := by norm_num

private theorem prime_oneHundredFortyNineEQ_326369 : Nat.Prime 326369 := by norm_num

private theorem prime_oneHundredFortyNineEQ_335449 : Nat.Prime 335449 := by norm_num

private theorem prime_oneHundredFortyNineEQ_366697 : Nat.Prime 366697 := by norm_num

private theorem prime_oneHundredFortyNineEQ_382763 : Nat.Prime 382763 := by norm_num

private theorem prime_oneHundredFortyNineEQ_404843 : Nat.Prime 404843 := by norm_num

private theorem prime_oneHundredFortyNineEQ_410143 : Nat.Prime 410143 := by norm_num

private theorem prime_oneHundredFortyNineEQ_436957 : Nat.Prime 436957 := by norm_num

private theorem prime_oneHundredFortyNineEQ_443659 : Nat.Prime 443659 := by norm_num

private theorem prime_oneHundredFortyNineEQ_449131 : Nat.Prime 449131 := by norm_num

private theorem prime_oneHundredFortyNineEQ_449971 : Nat.Prime 449971 := by norm_num

private theorem prime_oneHundredFortyNineEQ_469787 : Nat.Prime 469787 := by norm_num

private theorem prime_oneHundredFortyNineEQ_490001 : Nat.Prime 490001 := by norm_num

private theorem prime_oneHundredFortyNineEQ_526223 : Nat.Prime 526223 := by norm_num

private theorem prime_oneHundredFortyNineEQ_583409 : Nat.Prime 583409 := by norm_num

private theorem prime_oneHundredFortyNineEQ_594421 : Nat.Prime 594421 := by norm_num

private theorem prime_oneHundredFortyNineEQ_646379 : Nat.Prime 646379 := by norm_num

private theorem prime_oneHundredFortyNineEQ_656389 : Nat.Prime 656389 := by norm_num

private theorem prime_oneHundredFortyNineEQ_669913 : Nat.Prime 669913 := by norm_num

private theorem prime_oneHundredFortyNineEQ_728639 : Nat.Prime 728639 := by norm_num

private theorem prime_oneHundredFortyNineEQ_865829 : Nat.Prime 865829 := by norm_num

private theorem prime_oneHundredFortyNineEQ_911957 : Nat.Prime 911957 := by norm_num

private theorem prime_oneHundredFortyNineEQ_914533 : Nat.Prime 914533 := by norm_num

private theorem prime_oneHundredFortyNineEQ_938323 : Nat.Prime 938323 := by norm_num

private theorem prime_oneHundredFortyNineEQ_975217 : Nat.Prime 975217 := by norm_num

private theorem prime_oneHundredFortyNineEQ_992941 : Nat.Prime 992941 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1024547 : Nat.Prime 1024547 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1094237 : Nat.Prime 1094237 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1110643 : Nat.Prime 1110643 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1128577 : Nat.Prime 1128577 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1263259 : Nat.Prime 1263259 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1292549 : Nat.Prime 1292549 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1350469 : Nat.Prime 1350469 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1358803 : Nat.Prime 1358803 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1465481 : Nat.Prime 1465481 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1480621 : Nat.Prime 1480621 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1553803 : Nat.Prime 1553803 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1571183 : Nat.Prime 1571183 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1700851 : Nat.Prime 1700851 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1719967 : Nat.Prime 1719967 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1744697 : Nat.Prime 1744697 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1752403 : Nat.Prime 1752403 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1770773 : Nat.Prime 1770773 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1795957 : Nat.Prime 1795957 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1862359 : Nat.Prime 1862359 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1871929 : Nat.Prime 1871929 := by norm_num

private theorem prime_oneHundredFortyNineEQ_1977251 : Nat.Prime 1977251 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2274653 : Nat.Prime 2274653 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2300999 : Nat.Prime 2300999 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2302681 : Nat.Prime 2302681 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2381969 : Nat.Prime 2381969 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2576933 : Nat.Prime 2576933 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2611669 : Nat.Prime 2611669 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2627671 : Nat.Prime 2627671 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2759891 : Nat.Prime 2759891 := by norm_num

private theorem prime_oneHundredFortyNineEQ_2863969 : Nat.Prime 2863969 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3100087 : Nat.Prime 3100087 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3475601 : Nat.Prime 3475601 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3735371 : Nat.Prime 3735371 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3911539 : Nat.Prime 3911539 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3938251 : Nat.Prime 3938251 := by norm_num

private theorem prime_oneHundredFortyNineEQ_3967441 : Nat.Prime 3967441 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4256141 : Nat.Prime 4256141 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4507249 : Nat.Prime 4507249 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4720141 : Nat.Prime 4720141 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4778113 : Nat.Prime 4778113 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4807519 : Nat.Prime 4807519 := by norm_num

private theorem prime_oneHundredFortyNineEQ_4811777 : Nat.Prime 4811777 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5034233 : Nat.Prime 5034233 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5077249 : Nat.Prime 5077249 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5118871 : Nat.Prime 5118871 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5598449 : Nat.Prime 5598449 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5861299 : Nat.Prime 5861299 := by norm_num

private theorem prime_oneHundredFortyNineEQ_5935493 : Nat.Prime 5935493 := by norm_num

private theorem prime_oneHundredFortyNineEQ_6394723 : Nat.Prime 6394723 := by norm_num

private theorem prime_oneHundredFortyNineEQ_6633493 : Nat.Prime 6633493 := by norm_num

private theorem prime_oneHundredFortyNineEQ_6787349 : Nat.Prime 6787349 := by norm_num

private theorem prime_oneHundredFortyNineEQ_6856039 : Nat.Prime 6856039 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7053493 : Nat.Prime 7053493 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7258079 : Nat.Prime 7258079 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7425707 : Nat.Prime 7425707 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7624021 : Nat.Prime 7624021 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7632013 : Nat.Prime 7632013 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7726933 : Nat.Prime 7726933 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7875983 : Nat.Prime 7875983 := by norm_num

private theorem prime_oneHundredFortyNineEQ_7966759 : Nat.Prime 7966759 := by norm_num

private theorem prime_oneHundredFortyNineEQ_8923829 : Nat.Prime 8923829 := by norm_num

private theorem prime_oneHundredFortyNineEQ_10074671 : Nat.Prime 10074671 := by norm_num

private theorem prime_oneHundredFortyNineEQ_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFortyNineEQ_10994807 : Nat.Prime 10994807 := by norm_num

private theorem prime_oneHundredFortyNineEQ_11960527 : Nat.Prime 11960527 := by norm_num

private theorem prime_oneHundredFortyNineEQ_13572193 : Nat.Prime 13572193 := by norm_num

private theorem prime_oneHundredFortyNineEQ_14106181 : Nat.Prime 14106181 := by norm_num

private theorem prime_oneHundredFortyNineEQ_14839337 : Nat.Prime 14839337 := by norm_num

private theorem prime_oneHundredFortyNineEQ_16501123 : Nat.Prime 16501123 := by norm_num

private theorem prime_oneHundredFortyNineEQ_17841617 : Nat.Prime 17841617 := by norm_num

private theorem prime_oneHundredFortyNineEQ_19013987 : Nat.Prime 19013987 := by norm_num

private theorem prime_oneHundredFortyNineEQ_19404227 : Nat.Prime 19404227 := by norm_num

private theorem prime_oneHundredFortyNineEQ_20060611 : Nat.Prime 20060611 := by norm_num

private theorem prime_oneHundredFortyNineEQ_20703919 : Nat.Prime 20703919 := by norm_num

private theorem prime_oneHundredFortyNineEQ_24262313 : Nat.Prime 24262313 := by norm_num

private theorem prime_oneHundredFortyNineEQ_26791319 : Nat.Prime 26791319 := by norm_num

private theorem prime_oneHundredFortyNineEQ_30338227 : Nat.Prime 30338227 := by
  apply lucas_primality 30338227 (2 : ZMod 30338227)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (187273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (187273, 1)] : List FactorBlock).map factorBlockValue).prod) = 30338227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_187273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30338227) ^ 15169113 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 30338227) ^ 10112742 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 30338227) ^ 162 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_33458569 : Nat.Prime 33458569 := by
  apply lucas_primality 33458569 (31 : ZMod 33458569)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 1), (9749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 1), (9749, 1)] : List FactorBlock).map factorBlockValue).prod) = 33458569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_9749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 33458569) ^ 16729284 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (31 : ZMod 33458569) ^ 11152856 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (31 : ZMod 33458569) ^ 3041688 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (31 : ZMod 33458569) ^ 2573736 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (31 : ZMod 33458569) ^ 3432 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_43345663 : Nat.Prime 43345663 := by
  apply lucas_primality 43345663 (5 : ZMod 43345663)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (29, 1), (10831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (29, 1), (10831, 1)] : List FactorBlock).map factorBlockValue).prod) = 43345663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_23
      · exact prime_oneHundredFortyNineEQ_29
      · exact prime_oneHundredFortyNineEQ_10831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 43345663) ^ 21672831 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 43345663) ^ 14448554 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 43345663) ^ 1884594 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 43345663) ^ 1494678 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 43345663) ^ 4002 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_45984011 : Nat.Prime 45984011 := by
  apply lucas_primality 45984011 (2 : ZMod 45984011)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 2), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 2), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 45984011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_59
      · exact prime_oneHundredFortyNineEQ_1321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45984011) ^ 22992005 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 45984011) ^ 9196802 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 45984011) ^ 779390 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 45984011) ^ 34810 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_46539289 : Nat.Prime 46539289 := by
  apply lucas_primality 46539289 (7 : ZMod 46539289)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (646379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (646379, 1)] : List FactorBlock).map factorBlockValue).prod) = 46539289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_646379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 46539289) ^ 23269644 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 46539289) ^ 15513096 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 46539289) ^ 72 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_51275537 : Nat.Prime 51275537 := by
  apply lucas_primality 51275537 (3 : ZMod 51275537)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (17, 2), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (17, 2), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 51275537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 51275537) ^ 25637768 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51275537) ^ 3944272 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51275537) ^ 3016208 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51275537) ^ 60112 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_51551443 : Nat.Prime 51551443 := by
  apply lucas_primality 51551443 (2 : ZMod 51551443)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2863969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2863969, 1)] : List FactorBlock).map factorBlockValue).prod) = 51551443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_2863969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 51551443) ^ 25775721 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 51551443) ^ 17183814 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 51551443) ^ 18 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_51764563 : Nat.Prime 51764563 := by
  apply lucas_primality 51764563 (3 : ZMod 51764563)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (163, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (163, 1), (5881, 1)] : List FactorBlock).map factorBlockValue).prod) = 51764563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_163
      · exact prime_oneHundredFortyNineEQ_5881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 51764563) ^ 25882281 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51764563) ^ 17254854 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51764563) ^ 317574 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51764563) ^ 8802 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_53410271 : Nat.Prime 53410271 := by
  apply lucas_primality 53410271 (13 : ZMod 53410271)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1831, 1), (2917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1831, 1), (2917, 1)] : List FactorBlock).map factorBlockValue).prod) = 53410271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_1831
      · exact prime_oneHundredFortyNineEQ_2917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 53410271) ^ 26705135 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 53410271) ^ 10682054 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 53410271) ^ 29170 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 53410271) ^ 18310 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_55223977 : Nat.Prime 55223977 := by
  apply lucas_primality 55223977 (5 : ZMod 55223977)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2300999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2300999, 1)] : List FactorBlock).map factorBlockValue).prod) = 55223977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_2300999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 55223977) ^ 27611988 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 55223977) ^ 18407992 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 55223977) ^ 24 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_58795159 : Nat.Prime 58795159 := by
  apply lucas_primality 58795159 (3 : ZMod 58795159)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (31, 1), (127, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (31, 1), (127, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 58795159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_31
      · exact prime_oneHundredFortyNineEQ_127
      · exact prime_oneHundredFortyNineEQ_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 58795159) ^ 29397579 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58795159) ^ 19598386 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58795159) ^ 3094482 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58795159) ^ 1896618 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58795159) ^ 462954 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 58795159) ^ 448818 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_59845129 : Nat.Prime 59845129 := by
  apply lucas_primality 59845129 (13 : ZMod 59845129)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (31, 1), (11491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (31, 1), (11491, 1)] : List FactorBlock).map factorBlockValue).prod) = 59845129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_31
      · exact prime_oneHundredFortyNineEQ_11491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 59845129) ^ 29922564 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 59845129) ^ 19948376 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 59845129) ^ 8549304 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 59845129) ^ 1930488 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 59845129) ^ 5208 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_68541457 : Nat.Prime 68541457 := by
  apply lucas_primality 68541457 (5 : ZMod 68541457)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (139, 1), (10273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (139, 1), (10273, 1)] : List FactorBlock).map factorBlockValue).prod) = 68541457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_139
      · exact prime_oneHundredFortyNineEQ_10273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 68541457) ^ 34270728 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 68541457) ^ 22847152 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 68541457) ^ 493104 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 68541457) ^ 6672 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_79601917 : Nat.Prime 79601917 := by
  apply lucas_primality 79601917 (2 : ZMod 79601917)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6633493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6633493, 1)] : List FactorBlock).map factorBlockValue).prod) = 79601917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_6633493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 79601917) ^ 39800958 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 79601917) ^ 26533972 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 79601917) ^ 12 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_89474069 : Nat.Prime 89474069 := by
  apply lucas_primality 89474069 (2 : ZMod 89474069)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (366697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (366697, 1)] : List FactorBlock).map factorBlockValue).prod) = 89474069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_61
      · exact prime_oneHundredFortyNineEQ_366697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 89474069) ^ 44737034 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 89474069) ^ 1466788 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 89474069) ^ 244 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_91072727 : Nat.Prime 91072727 := by
  apply lucas_primality 91072727 (5 : ZMod 91072727)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (1110643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (1110643, 1)] : List FactorBlock).map factorBlockValue).prod) = 91072727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_41
      · exact prime_oneHundredFortyNineEQ_1110643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 91072727) ^ 45536363 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 91072727) ^ 2221286 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 91072727) ^ 82 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_91446317 : Nat.Prime 91446317 := by
  apply lucas_primality 91446317 (2 : ZMod 91446317)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (19, 1), (92557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (19, 1), (92557, 1)] : List FactorBlock).map factorBlockValue).prod) = 91446317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_92557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 91446317) ^ 45723158 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 91446317) ^ 7034332 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 91446317) ^ 4812964 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 91446317) ^ 988 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_92614853 : Nat.Prime 92614853 := by
  apply lucas_primality 92614853 (2 : ZMod 92614853)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (191353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (191353, 1)] : List FactorBlock).map factorBlockValue).prod) = 92614853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_191353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 92614853) ^ 46307426 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 92614853) ^ 8419532 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 92614853) ^ 484 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_94511797 : Nat.Prime 94511797 := by
  apply lucas_primality 94511797 (2 : ZMod 94511797)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7875983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7875983, 1)] : List FactorBlock).map factorBlockValue).prod) = 94511797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7875983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 94511797) ^ 47255898 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 94511797) ^ 31503932 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 94511797) ^ 12 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_96474863 : Nat.Prime 96474863 := by
  apply lucas_primality 96474863 (5 : ZMod 96474863)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (251, 1), (17471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (251, 1), (17471, 1)] : List FactorBlock).map factorBlockValue).prod) = 96474863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_251
      · exact prime_oneHundredFortyNineEQ_17471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 96474863) ^ 48237431 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 96474863) ^ 8770442 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 96474863) ^ 384362 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 96474863) ^ 5522 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_99356077 : Nat.Prime 99356077 := by
  apply lucas_primality 99356077 (2 : ZMod 99356077)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2759891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2759891, 1)] : List FactorBlock).map factorBlockValue).prod) = 99356077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_2759891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 99356077) ^ 49678038 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 99356077) ^ 33118692 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 99356077) ^ 36 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_101453993 : Nat.Prime 101453993 := by
  apply lucas_primality 101453993 (3 : ZMod 101453993)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1427, 1), (8887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1427, 1), (8887, 1)] : List FactorBlock).map factorBlockValue).prod) = 101453993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_1427
      · exact prime_oneHundredFortyNineEQ_8887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 101453993) ^ 50726996 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 101453993) ^ 71096 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 101453993) ^ 11416 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_104213453 : Nat.Prime 104213453 := by
  apply lucas_primality 104213453 (2 : ZMod 104213453)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1459, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1459, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) = 104213453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_1459
      · exact prime_oneHundredFortyNineEQ_2551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 104213453) ^ 52106726 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 104213453) ^ 14887636 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 104213453) ^ 71428 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 104213453) ^ 40852 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_105536603 : Nat.Prime 105536603 := by
  apply lucas_primality 105536603 (2 : ZMod 105536603)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (563, 1), (4933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (563, 1), (4933, 1)] : List FactorBlock).map factorBlockValue).prod) = 105536603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_563
      · exact prime_oneHundredFortyNineEQ_4933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105536603) ^ 52768301 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 105536603) ^ 5554558 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 105536603) ^ 187454 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 105536603) ^ 21394 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_105681467 : Nat.Prime 105681467 := by
  apply lucas_primality 105681467 (2 : ZMod 105681467)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (911, 1), (5273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (911, 1), (5273, 1)] : List FactorBlock).map factorBlockValue).prod) = 105681467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_911
      · exact prime_oneHundredFortyNineEQ_5273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 105681467) ^ 52840733 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 105681467) ^ 9607406 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 105681467) ^ 116006 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 105681467) ^ 20042 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_106564487 : Nat.Prime 106564487 := by
  apply lucas_primality 106564487 (5 : ZMod 106564487)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (941, 1), (8089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (941, 1), (8089, 1)] : List FactorBlock).map factorBlockValue).prod) = 106564487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_941
      · exact prime_oneHundredFortyNineEQ_8089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 106564487) ^ 53282243 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 106564487) ^ 15223498 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 106564487) ^ 113246 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 106564487) ^ 13174 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_111622961 : Nat.Prime 111622961 := by
  apply lucas_primality 111622961 (6 : ZMod 111622961)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (347, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (347, 1), (4021, 1)] : List FactorBlock).map factorBlockValue).prod) = 111622961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_347
      · exact prime_oneHundredFortyNineEQ_4021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 111622961) ^ 55811480 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 111622961) ^ 22324592 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 111622961) ^ 321680 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 111622961) ^ 27760 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_111720229 : Nat.Prime 111720229 := by
  apply lucas_primality 111720229 (2 : ZMod 111720229)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (490001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (490001, 1)] : List FactorBlock).map factorBlockValue).prod) = 111720229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_490001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 111720229) ^ 55860114 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 111720229) ^ 37240076 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 111720229) ^ 5880012 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 111720229) ^ 228 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_115231159 : Nat.Prime 115231159 := by
  apply lucas_primality 115231159 (3 : ZMod 115231159)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (914533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (914533, 1)] : List FactorBlock).map factorBlockValue).prod) = 115231159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_914533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 115231159) ^ 57615579 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 115231159) ^ 38410386 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 115231159) ^ 16461594 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 115231159) ^ 126 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_118060861 : Nat.Prime 118060861 := by
  apply lucas_primality 118060861 (11 : ZMod 118060861)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (83, 1), (151, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (83, 1), (151, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) = 118060861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_83
      · exact prime_oneHundredFortyNineEQ_151
      · exact prime_oneHundredFortyNineEQ_157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 118060861) ^ 59030430 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 118060861) ^ 39353620 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 118060861) ^ 23612172 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 118060861) ^ 1422420 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 118060861) ^ 781860 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 118060861) ^ 751980 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_123263993 : Nat.Prime 123263993 := by
  apply lucas_primality 123263993 (3 : ZMod 123263993)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (669913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (669913, 1)] : List FactorBlock).map factorBlockValue).prod) = 123263993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_23
      · exact prime_oneHundredFortyNineEQ_669913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 123263993) ^ 61631996 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 123263993) ^ 5359304 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 123263993) ^ 184 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_150654247 : Nat.Prime 150654247 := by
  apply lucas_primality 150654247 (5 : ZMod 150654247)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (865829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (865829, 1)] : List FactorBlock).map factorBlockValue).prod) = 150654247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_29
      · exact prime_oneHundredFortyNineEQ_865829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 150654247) ^ 75327123 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 150654247) ^ 50218082 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 150654247) ^ 5194974 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 150654247) ^ 174 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_167490913 : Nat.Prime 167490913 := by
  apply lucas_primality 167490913 (5 : ZMod 167490913)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1744697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1744697, 1)] : List FactorBlock).map factorBlockValue).prod) = 167490913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_1744697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 167490913) ^ 83745456 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 167490913) ^ 55830304 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 167490913) ^ 96 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_170616469 : Nat.Prime 170616469 := by
  apply lucas_primality 170616469 (14 : ZMod 170616469)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (1292549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (1292549, 1)] : List FactorBlock).map factorBlockValue).prod) = 170616469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_1292549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 170616469) ^ 85308234 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (14 : ZMod 170616469) ^ 56872156 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (14 : ZMod 170616469) ^ 15510588 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (14 : ZMod 170616469) ^ 132 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_173382653 : Nat.Prime 173382653 := by
  apply lucas_primality 173382653 (2 : ZMod 173382653)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43345663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43345663, 1)] : List FactorBlock).map factorBlockValue).prod) = 173382653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_43345663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 173382653) ^ 86691326 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173382653) ^ 4 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_201407863 : Nat.Prime 201407863 := by
  apply lucas_primality 201407863 (5 : ZMod 201407863)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (389, 1), (86293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (389, 1), (86293, 1)] : List FactorBlock).map factorBlockValue).prod) = 201407863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_389
      · exact prime_oneHundredFortyNineEQ_86293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 201407863) ^ 100703931 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 201407863) ^ 67135954 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 201407863) ^ 517758 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 201407863) ^ 2334 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_207377129 : Nat.Prime 207377129 := by
  apply lucas_primality 207377129 (3 : ZMod 207377129)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (53, 1), (107, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (53, 1), (107, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) = 207377129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_53
      · exact prime_oneHundredFortyNineEQ_107
      · exact prime_oneHundredFortyNineEQ_653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 207377129) ^ 103688564 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 207377129) ^ 29625304 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 207377129) ^ 3912776 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 207377129) ^ 1938104 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 207377129) ^ 317576 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_239079433 : Nat.Prime 239079433 := by
  apply lucas_primality 239079433 (7 : ZMod 239079433)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (19, 1), (30841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (19, 1), (30841, 1)] : List FactorBlock).map factorBlockValue).prod) = 239079433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_30841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 239079433) ^ 119539716 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 239079433) ^ 79693144 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 239079433) ^ 14063496 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 239079433) ^ 12583128 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 239079433) ^ 7752 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_239818763 : Nat.Prime 239818763 := by
  apply lucas_primality 239818763 (2 : ZMod 239818763)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (7053493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (7053493, 1)] : List FactorBlock).map factorBlockValue).prod) = 239818763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_7053493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 239818763) ^ 119909381 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 239818763) ^ 14106986 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 239818763) ^ 34 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_263701591 : Nat.Prime 263701591 := by
  apply lucas_primality 263701591 (6 : ZMod 263701591)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (353, 1), (673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (353, 1), (673, 1)] : List FactorBlock).map factorBlockValue).prod) = 263701591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_37
      · exact prime_oneHundredFortyNineEQ_353
      · exact prime_oneHundredFortyNineEQ_673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 263701591) ^ 131850795 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 263701591) ^ 87900530 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 263701591) ^ 52740318 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 263701591) ^ 7127070 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 263701591) ^ 747030 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 263701591) ^ 391830 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_264496109 : Nat.Prime 264496109 := by
  apply lucas_primality 264496109 (2 : ZMod 264496109)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (97, 1), (8629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (97, 1), (8629, 1)] : List FactorBlock).map factorBlockValue).prod) = 264496109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_79
      · exact prime_oneHundredFortyNineEQ_97
      · exact prime_oneHundredFortyNineEQ_8629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 264496109) ^ 132248054 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 264496109) ^ 3348052 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 264496109) ^ 2726764 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 264496109) ^ 30652 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_278691509 : Nat.Prime 278691509 := by
  apply lucas_primality 278691509 (3 : ZMod 278691509)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (953, 1), (2521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (953, 1), (2521, 1)] : List FactorBlock).map factorBlockValue).prod) = 278691509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_29
      · exact prime_oneHundredFortyNineEQ_953
      · exact prime_oneHundredFortyNineEQ_2521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 278691509) ^ 139345754 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 278691509) ^ 9610052 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 278691509) ^ 292436 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 278691509) ^ 110548 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_285068659 : Nat.Prime 285068659 := by
  apply lucas_primality 285068659 (3 : ZMod 285068659)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (6787349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (6787349, 1)] : List FactorBlock).map factorBlockValue).prod) = 285068659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_6787349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 285068659) ^ 142534329 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 285068659) ^ 95022886 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 285068659) ^ 40724094 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 285068659) ^ 42 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_285647317 : Nat.Prime 285647317 := by
  apply lucas_primality 285647317 (6 : ZMod 285647317)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (449131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (449131, 1)] : List FactorBlock).map factorBlockValue).prod) = 285647317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_53
      · exact prime_oneHundredFortyNineEQ_449131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 285647317) ^ 142823658 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 285647317) ^ 95215772 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 285647317) ^ 5389572 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 285647317) ^ 636 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_290002327 : Nat.Prime 290002327 := by
  apply lucas_primality 290002327 (3 : ZMod 290002327)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (911957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (911957, 1)] : List FactorBlock).map factorBlockValue).prod) = 290002327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_53
      · exact prime_oneHundredFortyNineEQ_911957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 290002327) ^ 145001163 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 290002327) ^ 96667442 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 290002327) ^ 5471742 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 290002327) ^ 318 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_327372079 : Nat.Prime 327372079 := by
  apply lucas_primality 327372079 (6 : ZMod 327372079)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (37, 1), (134059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (37, 1), (134059, 1)] : List FactorBlock).map factorBlockValue).prod) = 327372079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_37
      · exact prime_oneHundredFortyNineEQ_134059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 327372079) ^ 163686039 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 327372079) ^ 109124026 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 327372079) ^ 29761098 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 327372079) ^ 8847894 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 327372079) ^ 2442 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_347148433 : Nat.Prime 347148433 := by
  apply lucas_primality 347148433 (5 : ZMod 347148433)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (17, 1), (109, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (17, 1), (109, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) = 347148433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_109
      · exact prime_oneHundredFortyNineEQ_1301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 347148433) ^ 173574216 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 347148433) ^ 115716144 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 347148433) ^ 20420496 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 347148433) ^ 3184848 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 347148433) ^ 266832 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_391936267 : Nat.Prime 391936267 := by
  apply lucas_primality 391936267 (3 : ZMod 391936267)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7258079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7258079, 1)] : List FactorBlock).map factorBlockValue).prod) = 391936267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7258079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 391936267) ^ 195968133 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 391936267) ^ 130645422 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 391936267) ^ 54 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_498827731 : Nat.Prime 498827731 := by
  apply lucas_primality 498827731 (2 : ZMod 498827731)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (67, 1), (6053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (67, 1), (6053, 1)] : List FactorBlock).map factorBlockValue).prod) = 498827731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_41
      · exact prime_oneHundredFortyNineEQ_67
      · exact prime_oneHundredFortyNineEQ_6053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 498827731) ^ 249413865 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 498827731) ^ 166275910 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 498827731) ^ 99765546 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 498827731) ^ 12166530 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 498827731) ^ 7445190 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 498827731) ^ 82410 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_522914173 : Nat.Prime 522914173 := by
  apply lucas_primality 522914173 (2 : ZMod 522914173)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (229, 1), (17299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (229, 1), (17299, 1)] : List FactorBlock).map factorBlockValue).prod) = 522914173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_229
      · exact prime_oneHundredFortyNineEQ_17299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 522914173) ^ 261457086 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 522914173) ^ 174304724 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 522914173) ^ 47537652 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 522914173) ^ 2283468 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 522914173) ^ 30228 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_569197669 : Nat.Prime 569197669 := by
  apply lucas_primality 569197669 (6 : ZMod 569197669)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (19, 1), (192037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (19, 1), (192037, 1)] : List FactorBlock).map factorBlockValue).prod) = 569197669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_192037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 569197669) ^ 284598834 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 569197669) ^ 189732556 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 569197669) ^ 43784436 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 569197669) ^ 29957772 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 569197669) ^ 2964 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_639948277 : Nat.Prime 639948277 := by
  apply lucas_primality 639948277 (2 : ZMod 639948277)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 6), (11, 1), (71, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 6), (11, 1), (71, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) = 639948277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_71
      · exact prime_oneHundredFortyNineEQ_281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 639948277) ^ 319974138 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 639948277) ^ 213316092 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 639948277) ^ 58177116 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 639948277) ^ 9013356 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 639948277) ^ 2277396 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_17203
      · exact prime_oneHundredFortyNineEQ_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_718141549 : Nat.Prime 718141549 := by
  apply lucas_primality 718141549 (6 : ZMod 718141549)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59845129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59845129, 1)] : List FactorBlock).map factorBlockValue).prod) = 718141549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_59845129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 718141549) ^ 359070774 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 718141549) ^ 239380516 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 718141549) ^ 12 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_754750231 : Nat.Prime 754750231 := by
  apply lucas_primality 754750231 (3 : ZMod 754750231)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (29, 1), (66733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (29, 1), (66733, 1)] : List FactorBlock).map factorBlockValue).prod) = 754750231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_29
      · exact prime_oneHundredFortyNineEQ_66733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 754750231) ^ 377375115 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 754750231) ^ 251583410 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 754750231) ^ 150950046 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 754750231) ^ 58057710 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 754750231) ^ 26025870 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 754750231) ^ 11310 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_780520009 : Nat.Prime 780520009 := by
  apply lucas_primality 780520009 (21 : ZMod 780520009)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (131, 1), (248257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (131, 1), (248257, 1)] : List FactorBlock).map factorBlockValue).prod) = 780520009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_131
      · exact prime_oneHundredFortyNineEQ_248257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 780520009) ^ 390260004 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 780520009) ^ 260173336 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 780520009) ^ 5958168 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 780520009) ^ 3144 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_807344539 : Nat.Prime 807344539 := by
  apply lucas_primality 807344539 (7 : ZMod 807344539)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (229, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (229, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) = 807344539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_229
      · exact prime_oneHundredFortyNineEQ_587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 807344539) ^ 403672269 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 807344539) ^ 269114846 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 807344539) ^ 115334934 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 807344539) ^ 73394958 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 807344539) ^ 62103426 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 807344539) ^ 3525522 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 807344539) ^ 1375374 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_890105701 : Nat.Prime 890105701 := by
  apply lucas_primality 890105701 (6 : ZMod 890105701)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 1), (29, 1), (71, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 1), (29, 1), (71, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 890105701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_29
      · exact prime_oneHundredFortyNineEQ_71
      · exact prime_oneHundredFortyNineEQ_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 890105701) ^ 445052850 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 890105701) ^ 296701900 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 890105701) ^ 178021140 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 890105701) ^ 80918700 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 890105701) ^ 30693300 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 890105701) ^ 12536700 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 890105701) ^ 6794700 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_983665049 : Nat.Prime 983665049 := by
  apply lucas_primality 983665049 (3 : ZMod 983665049)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1861, 1), (66071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1861, 1), (66071, 1)] : List FactorBlock).map factorBlockValue).prod) = 983665049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_1861
      · exact prime_oneHundredFortyNineEQ_66071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 983665049) ^ 491832524 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 983665049) ^ 528568 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 983665049) ^ 14888 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1007064437 : Nat.Prime 1007064437 := by
  apply lucas_primality 1007064437 (3 : ZMod 1007064437)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (653, 1), (55079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (653, 1), (55079, 1)] : List FactorBlock).map factorBlockValue).prod) = 1007064437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_653
      · exact prime_oneHundredFortyNineEQ_55079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1007064437) ^ 503532218 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007064437) ^ 143866348 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007064437) ^ 1542212 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1007064437) ^ 18284 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1208447179 : Nat.Prime 1208447179 := by
  apply lucas_primality 1208447179 (2 : ZMod 1208447179)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (201407863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (201407863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1208447179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_201407863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1208447179) ^ 604223589 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1208447179) ^ 402815726 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1208447179) ^ 6 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1269335647 : Nat.Prime 1269335647 := by
  apply lucas_primality 1269335647 (3 : ZMod 1269335647)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (1719967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (1719967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1269335647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_41
      · exact prime_oneHundredFortyNineEQ_1719967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1269335647) ^ 634667823 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269335647) ^ 423111882 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269335647) ^ 30959406 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1269335647) ^ 738 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1302012319 : Nat.Prime 1302012319 := by
  apply lucas_primality 1302012319 (3 : ZMod 1302012319)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (1217, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (1217, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) = 1302012319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_41
      · exact prime_oneHundredFortyNineEQ_1217
      · exact prime_oneHundredFortyNineEQ_4349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1302012319) ^ 651006159 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1302012319) ^ 434004106 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1302012319) ^ 31756398 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1302012319) ^ 1069854 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1302012319) ^ 299382 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1347277111 : Nat.Prime 1347277111 := by
  apply lucas_primality 1347277111 (3 : ZMod 1347277111)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (461, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (461, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) = 1347277111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_61
      · exact prime_oneHundredFortyNineEQ_461
      · exact prime_oneHundredFortyNineEQ_1597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1347277111) ^ 673638555 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1347277111) ^ 449092370 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1347277111) ^ 269455422 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1347277111) ^ 22086510 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1347277111) ^ 2922510 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1347277111) ^ 843630 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1356359923 : Nat.Prime 1356359923 := by
  apply lucas_primality 1356359923 (2 : ZMod 1356359923)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (1752403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (1752403, 1)] : List FactorBlock).map factorBlockValue).prod) = 1356359923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_43
      · exact prime_oneHundredFortyNineEQ_1752403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1356359923) ^ 678179961 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1356359923) ^ 452119974 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1356359923) ^ 31543254 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1356359923) ^ 774 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1363412131 : Nat.Prime 1363412131 := by
  apply lucas_primality 1363412131 (2 : ZMod 1363412131)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (449971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (449971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1363412131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_101
      · exact prime_oneHundredFortyNineEQ_449971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1363412131) ^ 681706065 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1363412131) ^ 454470710 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1363412131) ^ 272682426 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1363412131) ^ 13499130 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1363412131) ^ 3030 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1470540083 : Nat.Prime 1470540083 := by
  apply lucas_primality 1470540083 (5 : ZMod 1470540083)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (5867, 1), (11393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (5867, 1), (11393, 1)] : List FactorBlock).map factorBlockValue).prod) = 1470540083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_5867
      · exact prime_oneHundredFortyNineEQ_11393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1470540083) ^ 735270041 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1470540083) ^ 133685462 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1470540083) ^ 250646 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1470540083) ^ 129074 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1484427149 : Nat.Prime 1484427149 := by
  apply lucas_primality 1484427149 (2 : ZMod 1484427149)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (139, 1), (157049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (139, 1), (157049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1484427149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_139
      · exact prime_oneHundredFortyNineEQ_157049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1484427149) ^ 742213574 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1484427149) ^ 87319244 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1484427149) ^ 10679332 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1484427149) ^ 9452 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1674870403 : Nat.Prime 1674870403 := by
  apply lucas_primality 1674870403 (2 : ZMod 1674870403)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5923, 1), (47129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5923, 1), (47129, 1)] : List FactorBlock).map factorBlockValue).prod) = 1674870403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5923
      · exact prime_oneHundredFortyNineEQ_47129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1674870403) ^ 837435201 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674870403) ^ 558290134 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674870403) ^ 282774 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1674870403) ^ 35538 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1808649511 : Nat.Prime 1808649511 := by
  apply lucas_primality 1808649511 (6 : ZMod 1808649511)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (863, 1), (69859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (863, 1), (69859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1808649511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_863
      · exact prime_oneHundredFortyNineEQ_69859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1808649511) ^ 904324755 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1808649511) ^ 602883170 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1808649511) ^ 361729902 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1808649511) ^ 2095770 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1808649511) ^ 25890 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2159283811 : Nat.Prime 2159283811 := by
  apply lucas_primality 2159283811 (2 : ZMod 2159283811)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2053, 1), (35059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2053, 1), (35059, 1)] : List FactorBlock).map factorBlockValue).prod) = 2159283811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_2053
      · exact prime_oneHundredFortyNineEQ_35059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2159283811) ^ 1079641905 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2159283811) ^ 719761270 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2159283811) ^ 431856762 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2159283811) ^ 1051770 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2159283811) ^ 61590 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2196269429 : Nat.Prime 2196269429 := by
  apply lucas_primality 2196269429 (2 : ZMod 2196269429)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1789, 1), (306913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1789, 1), (306913, 1)] : List FactorBlock).map factorBlockValue).prod) = 2196269429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_1789
      · exact prime_oneHundredFortyNineEQ_306913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2196269429) ^ 1098134714 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2196269429) ^ 1227652 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2196269429) ^ 7156 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2410180361 : Nat.Prime 2410180361 := by
  apply lucas_primality 2410180361 (3 : ZMod 2410180361)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (691, 1), (12457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (691, 1), (12457, 1)] : List FactorBlock).map factorBlockValue).prod) = 2410180361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_691
      · exact prime_oneHundredFortyNineEQ_12457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2410180361) ^ 1205090180 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2410180361) ^ 482036072 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2410180361) ^ 344311480 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2410180361) ^ 3487960 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2410180361) ^ 193480 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2721725117 : Nat.Prime 2721725117 := by
  apply lucas_primality 2721725117 (2 : ZMod 2721725117)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (419, 1), (13421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (419, 1), (13421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2721725117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_419
      · exact prime_oneHundredFortyNineEQ_13421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2721725117) ^ 1360862558 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2721725117) ^ 247429556 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2721725117) ^ 6495764 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2721725117) ^ 202796 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2844626527 : Nat.Prime 2844626527 := by
  apply lucas_primality 2844626527 (7 : ZMod 2844626527)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 11), (7, 1), (31, 1), (37, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 11), (7, 1), (31, 1), (37, 1)] : List FactorBlock).map factorBlockValue).prod) = 2844626527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_31
      · exact prime_oneHundredFortyNineEQ_37
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2844626527) ^ 1422313263 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2844626527) ^ 948208842 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2844626527) ^ 406375218 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2844626527) ^ 91762146 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2844626527) ^ 76881798 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2865669013 : Nat.Prime 2865669013 := by
  apply lucas_primality 2865669013 (2 : ZMod 2865669013)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79601917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79601917, 1)] : List FactorBlock).map factorBlockValue).prod) = 2865669013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_79601917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2865669013) ^ 1432834506 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2865669013) ^ 955223004 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2865669013) ^ 36 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2871430073 : Nat.Prime 2871430073 := by
  apply lucas_primality 2871430073 (6 : ZMod 2871430073)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (51275537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (51275537, 1)] : List FactorBlock).map factorBlockValue).prod) = 2871430073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_51275537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 2871430073) ^ 1435715036 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 2871430073) ^ 410204296 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 2871430073) ^ 56 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2968854299 : Nat.Prime 2968854299 := by
  apply lucas_primality 2968854299 (2 : ZMod 2968854299)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1484427149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1484427149, 1)] : List FactorBlock).map factorBlockValue).prod) = 2968854299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_1484427149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2968854299) ^ 1484427149 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2968854299) ^ 2 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2997813257 : Nat.Prime 2997813257 := by
  apply lucas_primality 2997813257 (3 : ZMod 2997813257)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (83, 1), (883, 1), (5113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (83, 1), (883, 1), (5113, 1)] : List FactorBlock).map factorBlockValue).prod) = 2997813257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_83
      · exact prime_oneHundredFortyNineEQ_883
      · exact prime_oneHundredFortyNineEQ_5113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2997813257) ^ 1498906628 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2997813257) ^ 36118232 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2997813257) ^ 3395032 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2997813257) ^ 586312 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_4214200031 : Nat.Prime 4214200031 := by
  apply lucas_primality 4214200031 (13 : ZMod 4214200031)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (5935493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (5935493, 1)] : List FactorBlock).map factorBlockValue).prod) = 4214200031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_71
      · exact prime_oneHundredFortyNineEQ_5935493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4214200031) ^ 2107100015 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 4214200031) ^ 842840006 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 4214200031) ^ 59354930 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 4214200031) ^ 710 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_4392538859 : Nat.Prime 4392538859 := by
  apply lucas_primality 4392538859 (2 : ZMod 4392538859)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2196269429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2196269429, 1)] : List FactorBlock).map factorBlockValue).prod) = 4392538859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_2196269429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4392538859) ^ 2196269429 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4392538859) ^ 2 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_4412250581 : Nat.Prime 4412250581 := by
  apply lucas_primality 4412250581 (2 : ZMod 4412250581)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (149, 1), (1480621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (149, 1), (1480621, 1)] : List FactorBlock).map factorBlockValue).prod) = 4412250581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_149
      · exact prime_oneHundredFortyNineEQ_1480621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4412250581) ^ 2206125290 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4412250581) ^ 882450116 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4412250581) ^ 29612420 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4412250581) ^ 2980 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_4618527019 : Nat.Prime 4618527019 := by
  apply lucas_primality 4618527019 (2 : ZMod 4618527019)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (227, 1), (5443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (227, 1), (5443, 1)] : List FactorBlock).map factorBlockValue).prod) = 4618527019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_89
      · exact prime_oneHundredFortyNineEQ_227
      · exact prime_oneHundredFortyNineEQ_5443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4618527019) ^ 2309263509 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4618527019) ^ 1539509006 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4618527019) ^ 659789574 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4618527019) ^ 51893562 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4618527019) ^ 20345934 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4618527019) ^ 848526 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_4892494489 : Nat.Prime 4892494489 := by
  apply lucas_primality 4892494489 (19 : ZMod 4892494489)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (5119, 1), (5689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (5119, 1), (5689, 1)] : List FactorBlock).map factorBlockValue).prod) = 4892494489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_5119
      · exact prime_oneHundredFortyNineEQ_5689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 4892494489) ^ 2446247244 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (19 : ZMod 4892494489) ^ 1630831496 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (19 : ZMod 4892494489) ^ 698927784 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (19 : ZMod 4892494489) ^ 955752 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (19 : ZMod 4892494489) ^ 859992 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_5365465817 : Nat.Prime 5365465817 := by
  apply lucas_primality 5365465817 (3 : ZMod 5365465817)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (10994807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (10994807, 1)] : List FactorBlock).map factorBlockValue).prod) = 5365465817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_61
      · exact prime_oneHundredFortyNineEQ_10994807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5365465817) ^ 2682732908 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5365465817) ^ 87958456 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5365465817) ^ 488 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_5630054623 : Nat.Prime 5630054623 := by
  apply lucas_primality 5630054623 (5 : ZMod 5630054623)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (2699, 1), (5189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (2699, 1), (5189, 1)] : List FactorBlock).map factorBlockValue).prod) = 5630054623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_67
      · exact prime_oneHundredFortyNineEQ_2699
      · exact prime_oneHundredFortyNineEQ_5189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5630054623) ^ 2815027311 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 5630054623) ^ 1876684874 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 5630054623) ^ 84030666 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 5630054623) ^ 2085978 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 5630054623) ^ 1084998 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_5754885293 : Nat.Prime 5754885293 := by
  apply lucas_primality 5754885293 (3 : ZMod 5754885293)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (23, 1), (4811777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (23, 1), (4811777, 1)] : List FactorBlock).map factorBlockValue).prod) = 5754885293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_23
      · exact prime_oneHundredFortyNineEQ_4811777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5754885293) ^ 2877442646 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5754885293) ^ 442683484 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5754885293) ^ 250212404 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5754885293) ^ 1196 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_31
      · exact prime_oneHundredFortyNineEQ_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_7583544071 : Nat.Prime 7583544071 := by
  apply lucas_primality 7583544071 (11 : ZMod 7583544071)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 2), (410143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 2), (410143, 1)] : List FactorBlock).map factorBlockValue).prod) = 7583544071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_43
      · exact prime_oneHundredFortyNineEQ_410143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7583544071) ^ 3791772035 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7583544071) ^ 1516708814 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7583544071) ^ 176361490 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 7583544071) ^ 18490 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_8824501163 : Nat.Prime 8824501163 := by
  apply lucas_primality 8824501163 (2 : ZMod 8824501163)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4412250581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4412250581, 1)] : List FactorBlock).map factorBlockValue).prod) = 8824501163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_4412250581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 8824501163) ^ 4412250581 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8824501163) ^ 2 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_9949332223 : Nat.Prime 9949332223 := by
  apply lucas_primality 9949332223 (3 : ZMod 9949332223)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (2274653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (2274653, 1)] : List FactorBlock).map factorBlockValue).prod) = 9949332223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_2274653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9949332223) ^ 4974666111 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 9949332223) ^ 3316444074 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 9949332223) ^ 4374 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_10680071377 : Nat.Prime 10680071377 := by
  apply lucas_primality 10680071377 (5 : ZMod 10680071377)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (997, 1), (17167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (997, 1), (17167, 1)] : List FactorBlock).map factorBlockValue).prod) = 10680071377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_997
      · exact prime_oneHundredFortyNineEQ_17167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10680071377) ^ 5340035688 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 10680071377) ^ 3560023792 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 10680071377) ^ 821543952 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 10680071377) ^ 10712208 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 10680071377) ^ 622128 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_11547902461 : Nat.Prime 11547902461 := by
  apply lucas_primality 11547902461 (11 : ZMod 11547902461)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 2), (19, 1), (35051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 2), (19, 1), (35051, 1)] : List FactorBlock).map factorBlockValue).prod) = 11547902461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_35051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11547902461) ^ 5773951230 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 11547902461) ^ 3849300820 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 11547902461) ^ 2309580492 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 11547902461) ^ 679288380 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 11547902461) ^ 607784340 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 11547902461) ^ 329460 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_12776668363 : Nat.Prime 12776668363 := by
  apply lucas_primality 12776668363 (2 : ZMod 12776668363)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7489, 1), (94781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7489, 1), (94781, 1)] : List FactorBlock).map factorBlockValue).prod) = 12776668363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7489
      · exact prime_oneHundredFortyNineEQ_94781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12776668363) ^ 6388334181 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12776668363) ^ 4258889454 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12776668363) ^ 1706058 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12776668363) ^ 134802 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_13371140273 : Nat.Prime 13371140273 := by
  apply lucas_primality 13371140273 (3 : ZMod 13371140273)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (617, 1), (193493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (617, 1), (193493, 1)] : List FactorBlock).map factorBlockValue).prod) = 13371140273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_617
      · exact prime_oneHundredFortyNineEQ_193493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13371140273) ^ 6685570136 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13371140273) ^ 1910162896 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13371140273) ^ 21671216 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 13371140273) ^ 69104 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_15341747261 : Nat.Prime 15341747261 := by
  apply lucas_primality 15341747261 (10 : ZMod 15341747261)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (43, 1), (173, 1), (14731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (43, 1), (173, 1), (14731, 1)] : List FactorBlock).map factorBlockValue).prod) = 15341747261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_43
      · exact prime_oneHundredFortyNineEQ_173
      · exact prime_oneHundredFortyNineEQ_14731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 15341747261) ^ 7670873630 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 15341747261) ^ 3068349452 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 15341747261) ^ 2191678180 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 15341747261) ^ 356784820 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 15341747261) ^ 88680620 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 15341747261) ^ 1041460 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_16715885089 : Nat.Prime 16715885089 := by
  apply lucas_primality 16715885089 (11 : ZMod 16715885089)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 2), (397, 1), (8951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 2), (397, 1), (8951, 1)] : List FactorBlock).map factorBlockValue).prod) = 16715885089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_397
      · exact prime_oneHundredFortyNineEQ_8951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 16715885089) ^ 8357942544 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 16715885089) ^ 5571961696 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 16715885089) ^ 2387983584 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 16715885089) ^ 42105504 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 16715885089) ^ 1867488 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_17372978951 : Nat.Prime 17372978951 := by
  apply lucas_primality 17372978951 (11 : ZMod 17372978951)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (47, 1), (317, 1), (23321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (47, 1), (317, 1), (23321, 1)] : List FactorBlock).map factorBlockValue).prod) = 17372978951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_47
      · exact prime_oneHundredFortyNineEQ_317
      · exact prime_oneHundredFortyNineEQ_23321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 17372978951) ^ 8686489475 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 17372978951) ^ 3474595790 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 17372978951) ^ 369637850 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 17372978951) ^ 54804350 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 17372978951) ^ 744950 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_22625034401 : Nat.Prime 22625034401 := by
  apply lucas_primality 22625034401 (13 : ZMod 22625034401)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (29, 1), (975217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (29, 1), (975217, 1)] : List FactorBlock).map factorBlockValue).prod) = 22625034401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_29
      · exact prime_oneHundredFortyNineEQ_975217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 22625034401) ^ 11312517200 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 22625034401) ^ 4525006880 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 22625034401) ^ 780173600 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 22625034401) ^ 23200 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_24333805499 : Nat.Prime 24333805499 := by
  apply lucas_primality 24333805499 (2 : ZMod 24333805499)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (111622961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (111622961, 1)] : List FactorBlock).map factorBlockValue).prod) = 24333805499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_109
      · exact prime_oneHundredFortyNineEQ_111622961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24333805499) ^ 12166902749 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 24333805499) ^ 223245922 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 24333805499) ^ 218 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_24930762629 : Nat.Prime 24930762629 := by
  apply lucas_primality 24930762629 (2 : ZMod 24930762629)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6277, 1), (992941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6277, 1), (992941, 1)] : List FactorBlock).map factorBlockValue).prod) = 24930762629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_6277
      · exact prime_oneHundredFortyNineEQ_992941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24930762629) ^ 12465381314 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 24930762629) ^ 3971764 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 24930762629) ^ 25108 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_26537680307 : Nat.Prime 26537680307 := by
  apply lucas_primality 26537680307 (2 : ZMod 26537680307)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (780520009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (780520009, 1)] : List FactorBlock).map factorBlockValue).prod) = 26537680307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_780520009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26537680307) ^ 13268840153 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 26537680307) ^ 1561040018 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 26537680307) ^ 34 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_29929663861 : Nat.Prime 29929663861 := by
  apply lucas_primality 29929663861 (6 : ZMod 29929663861)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (498827731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (498827731, 1)] : List FactorBlock).map factorBlockValue).prod) = 29929663861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_498827731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 29929663861) ^ 14964831930 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 29929663861) ^ 9976554620 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 29929663861) ^ 5985932772 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 29929663861) ^ 60 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_33842006903 : Nat.Prime 33842006903 := by
  apply lucas_primality 33842006903 (5 : ZMod 33842006903)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (31, 1), (2611669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (31, 1), (2611669, 1)] : List FactorBlock).map factorBlockValue).prod) = 33842006903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_31
      · exact prime_oneHundredFortyNineEQ_2611669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33842006903) ^ 16921003451 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 33842006903) ^ 3076546082 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 33842006903) ^ 1781158258 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 33842006903) ^ 1091677642 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 33842006903) ^ 12958 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_34601010113 : Nat.Prime 34601010113 := by
  apply lucas_primality 34601010113 (3 : ZMod 34601010113)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (17, 1), (23, 1), (853, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (17, 1), (23, 1), (853, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) = 34601010113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_23
      · exact prime_oneHundredFortyNineEQ_853
      · exact prime_oneHundredFortyNineEQ_1621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34601010113) ^ 17300505056 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 34601010113) ^ 2035353536 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 34601010113) ^ 1504391744 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 34601010113) ^ 40563904 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 34601010113) ^ 21345472 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_41652209843 : Nat.Prime 41652209843 := by
  apply lucas_primality 41652209843 (2 : ZMod 41652209843)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (718141549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (718141549, 1)] : List FactorBlock).map factorBlockValue).prod) = 41652209843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_29
      · exact prime_oneHundredFortyNineEQ_718141549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41652209843) ^ 20826104921 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 41652209843) ^ 1436283098 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 41652209843) ^ 58 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_41846434547 : Nat.Prime 41846434547 := by
  apply lucas_primality 41846434547 (5 : ZMod 41846434547)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (149, 1), (20060611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (149, 1), (20060611, 1)] : List FactorBlock).map factorBlockValue).prod) = 41846434547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_149
      · exact prime_oneHundredFortyNineEQ_20060611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 41846434547) ^ 20923217273 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 41846434547) ^ 5978062078 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 41846434547) ^ 280848554 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 41846434547) ^ 2086 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_46958631121 : Nat.Prime 46958631121 := by
  apply lucas_primality 46958631121 (11 : ZMod 46958631121)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (83, 1), (103, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (83, 1), (103, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) = 46958631121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_83
      · exact prime_oneHundredFortyNineEQ_103
      · exact prime_oneHundredFortyNineEQ_2543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 46958631121) ^ 23479315560 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 46958631121) ^ 15652877040 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 46958631121) ^ 9391726224 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 46958631121) ^ 565766640 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 46958631121) ^ 455909040 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 46958631121) ^ 18465840 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_50037012299 : Nat.Prime 50037012299 := by
  apply lucas_primality 50037012299 (2 : ZMod 50037012299)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (293, 1), (938323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (293, 1), (938323, 1)] : List FactorBlock).map factorBlockValue).prod) = 50037012299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_293
      · exact prime_oneHundredFortyNineEQ_938323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50037012299) ^ 25018506149 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 50037012299) ^ 7148144614 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 50037012299) ^ 3849000946 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 50037012299) ^ 170774786 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 50037012299) ^ 53326 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_68270637091 : Nat.Prime 68270637091 := by
  apply lucas_primality 68270637091 (2 : ZMod 68270637091)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (89, 1), (113, 1), (5519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (89, 1), (113, 1), (5519, 1)] : List FactorBlock).map factorBlockValue).prod) = 68270637091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_41
      · exact prime_oneHundredFortyNineEQ_89
      · exact prime_oneHundredFortyNineEQ_113
      · exact prime_oneHundredFortyNineEQ_5519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68270637091) ^ 34135318545 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68270637091) ^ 22756879030 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68270637091) ^ 13654127418 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68270637091) ^ 1665137490 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68270637091) ^ 767085810 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68270637091) ^ 604164930 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68270637091) ^ 12370110 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_69216950461 : Nat.Prime 69216950461 := by
  apply lucas_primality 69216950461 (2 : ZMod 69216950461)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (10909, 1), (15107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (10909, 1), (15107, 1)] : List FactorBlock).map factorBlockValue).prod) = 69216950461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_10909
      · exact prime_oneHundredFortyNineEQ_15107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 69216950461) ^ 34608475230 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 69216950461) ^ 23072316820 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 69216950461) ^ 13843390092 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 69216950461) ^ 9888135780 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 69216950461) ^ 6344940 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 69216950461) ^ 4581780 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_70836516601 : Nat.Prime 70836516601 := by
  apply lucas_primality 70836516601 (17 : ZMod 70836516601)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (118060861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (118060861, 1)] : List FactorBlock).map factorBlockValue).prod) = 70836516601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_118060861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 70836516601) ^ 35418258300 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 70836516601) ^ 23612172200 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 70836516601) ^ 14167303320 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 70836516601) ^ 600 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_75466745441 : Nat.Prime 75466745441 := by
  apply lucas_primality 75466745441 (3 : ZMod 75466745441)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (17, 1), (89, 1), (311743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (17, 1), (89, 1), (311743, 1)] : List FactorBlock).map factorBlockValue).prod) = 75466745441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_89
      · exact prime_oneHundredFortyNineEQ_311743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75466745441) ^ 37733372720 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 75466745441) ^ 15093349088 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 75466745441) ^ 4439220320 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 75466745441) ^ 847940960 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 75466745441) ^ 242080 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_83304419687 : Nat.Prime 83304419687 := by
  apply lucas_primality 83304419687 (5 : ZMod 83304419687)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41652209843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41652209843, 1)] : List FactorBlock).map factorBlockValue).prod) = 83304419687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_41652209843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 83304419687) ^ 41652209843 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 83304419687) ^ 2 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_102143663597 : Nat.Prime 102143663597 := by
  apply lucas_primality 102143663597 (2 : ZMod 102143663597)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (23, 1), (2939, 1), (29059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (23, 1), (2939, 1), (29059, 1)] : List FactorBlock).map factorBlockValue).prod) = 102143663597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_23
      · exact prime_oneHundredFortyNineEQ_2939
      · exact prime_oneHundredFortyNineEQ_29059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102143663597) ^ 51071831798 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 102143663597) ^ 7857204892 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 102143663597) ^ 4441028852 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 102143663597) ^ 34754564 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 102143663597) ^ 3515044 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_121216768451 : Nat.Prime 121216768451 := by
  apply lucas_primality 121216768451 (2 : ZMod 121216768451)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1543, 1), (1571183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1543, 1), (1571183, 1)] : List FactorBlock).map factorBlockValue).prod) = 121216768451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_1543
      · exact prime_oneHundredFortyNineEQ_1571183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 121216768451) ^ 60608384225 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 121216768451) ^ 24243353690 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 121216768451) ^ 78559150 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 121216768451) ^ 77150 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_125207155939 : Nat.Prime 125207155939 := by
  apply lucas_primality 125207155939 (2 : ZMod 125207155939)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4903, 1), (4256141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4903, 1), (4256141, 1)] : List FactorBlock).map factorBlockValue).prod) = 125207155939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_4903
      · exact prime_oneHundredFortyNineEQ_4256141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 125207155939) ^ 62603577969 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 125207155939) ^ 41735718646 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 125207155939) ^ 25536846 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 125207155939) ^ 29418 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_144338459891 : Nat.Prime 144338459891 := by
  apply lucas_primality 144338459891 (2 : ZMod 144338459891)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (293, 1), (547, 1), (90059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (293, 1), (547, 1), (90059, 1)] : List FactorBlock).map factorBlockValue).prod) = 144338459891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_293
      · exact prime_oneHundredFortyNineEQ_547
      · exact prime_oneHundredFortyNineEQ_90059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 144338459891) ^ 72169229945 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 144338459891) ^ 28867691978 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 144338459891) ^ 492622730 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 144338459891) ^ 263872870 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 144338459891) ^ 1602710 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_152416606553 : Nat.Prime 152416606553 := by
  apply lucas_primality 152416606553 (3 : ZMod 152416606553)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (2721725117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (2721725117, 1)] : List FactorBlock).map factorBlockValue).prod) = 152416606553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_2721725117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 152416606553) ^ 76208303276 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 152416606553) ^ 21773800936 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 152416606553) ^ 56 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_159396173977 : Nat.Prime 159396173977 := by
  apply lucas_primality 159396173977 (5 : ZMod 159396173977)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (17, 1), (313, 1), (96013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (17, 1), (313, 1), (96013, 1)] : List FactorBlock).map factorBlockValue).prod) = 159396173977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_313
      · exact prime_oneHundredFortyNineEQ_96013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 159396173977) ^ 79698086988 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 159396173977) ^ 53132057992 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 159396173977) ^ 12261244152 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 159396173977) ^ 9376245528 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 159396173977) ^ 509252952 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 159396173977) ^ 1660152 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_161548000531 : Nat.Prime 161548000531 := by
  apply lucas_primality 161548000531 (3 : ZMod 161548000531)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (23, 1), (4778113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (23, 1), (4778113, 1)] : List FactorBlock).map factorBlockValue).prod) = 161548000531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_23
      · exact prime_oneHundredFortyNineEQ_4778113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 161548000531) ^ 80774000265 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 161548000531) ^ 53849333510 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 161548000531) ^ 32309600106 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 161548000531) ^ 23078285790 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 161548000531) ^ 7023826110 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 161548000531) ^ 33810 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_170584329373 : Nat.Prime 170584329373 := by
  apply lucas_primality 170584329373 (2 : ZMod 170584329373)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (83, 1), (10074671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (83, 1), (10074671, 1)] : List FactorBlock).map factorBlockValue).prod) = 170584329373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_83
      · exact prime_oneHundredFortyNineEQ_10074671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 170584329373) ^ 85292164686 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 170584329373) ^ 56861443124 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 170584329373) ^ 10034372316 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 170584329373) ^ 2055232884 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 170584329373) ^ 16932 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_353887535123 : Nat.Prime 353887535123 := by
  apply lucas_primality 353887535123 (2 : ZMod 353887535123)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (263701591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (263701591, 1)] : List FactorBlock).map factorBlockValue).prod) = 353887535123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_61
      · exact prime_oneHundredFortyNineEQ_263701591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 353887535123) ^ 176943767561 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 353887535123) ^ 32171594102 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 353887535123) ^ 5801435002 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 353887535123) ^ 1342 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_409623822547 : Nat.Prime 409623822547 := by
  apply lucas_primality 409623822547 (2 : ZMod 409623822547)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (68270637091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (68270637091, 1)] : List FactorBlock).map factorBlockValue).prod) = 409623822547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_68270637091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 409623822547) ^ 204811911273 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 409623822547) ^ 136541274182 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 409623822547) ^ 6 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_499941619201 : Nat.Prime 499941619201 := by
  apply lucas_primality 499941619201 (11 : ZMod 499941619201)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 2), (5, 2), (19, 1), (228409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 2), (5, 2), (19, 1), (228409, 1)] : List FactorBlock).map factorBlockValue).prod) = 499941619201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_228409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 499941619201) ^ 249970809600 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 499941619201) ^ 166647206400 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 499941619201) ^ 99988323840 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 499941619201) ^ 26312716800 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 499941619201) ^ 2188800 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_557217104351 : Nat.Prime 557217104351 := by
  apply lucas_primality 557217104351 (13 : ZMod 557217104351)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (751, 1), (14839337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (751, 1), (14839337, 1)] : List FactorBlock).map factorBlockValue).prod) = 557217104351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_751
      · exact prime_oneHundredFortyNineEQ_14839337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 557217104351) ^ 278608552175 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 557217104351) ^ 111443420870 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 557217104351) ^ 741966850 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 557217104351) ^ 37550 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1208189562871 : Nat.Prime 1208189562871 := by
  apply lucas_primality 1208189562871 (3 : ZMod 1208189562871)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (6871, 1), (5861299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (6871, 1), (5861299, 1)] : List FactorBlock).map factorBlockValue).prod) = 1208189562871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_6871
      · exact prime_oneHundredFortyNineEQ_5861299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1208189562871) ^ 604094781435 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1208189562871) ^ 402729854290 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1208189562871) ^ 241637912574 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1208189562871) ^ 175838970 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1208189562871) ^ 206130 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1629907296733 : Nat.Prime 1629907296733 := by
  apply lucas_primality 1629907296733 (2 : ZMod 1629907296733)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (13, 1), (105536603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (13, 1), (105536603, 1)] : List FactorBlock).map factorBlockValue).prod) = 1629907296733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_105536603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1629907296733) ^ 814953648366 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1629907296733) ^ 543302432244 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1629907296733) ^ 148173390612 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1629907296733) ^ 125377484364 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1629907296733) ^ 15444 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1747211259841 : Nat.Prime 1747211259841 := by
  apply lucas_primality 1747211259841 (14 : ZMod 1747211259841)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (19, 1), (1373, 1), (69767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (19, 1), (1373, 1), (69767, 1)] : List FactorBlock).map factorBlockValue).prod) = 1747211259841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_1373
      · exact prime_oneHundredFortyNineEQ_69767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1747211259841) ^ 873605629920 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (14 : ZMod 1747211259841) ^ 582403753280 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (14 : ZMod 1747211259841) ^ 349442251968 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (14 : ZMod 1747211259841) ^ 91958487360 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (14 : ZMod 1747211259841) ^ 1272550080 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (14 : ZMod 1747211259841) ^ 25043520 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1751014665391 : Nat.Prime 1751014665391 := by
  apply lucas_primality 1751014665391 (21 : ZMod 1751014665391)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (16963, 1), (202403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (16963, 1), (202403, 1)] : List FactorBlock).map factorBlockValue).prod) = 1751014665391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_16963
      · exact prime_oneHundredFortyNineEQ_202403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 1751014665391) ^ 875507332695 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 1751014665391) ^ 583671555130 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 1751014665391) ^ 350202933078 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 1751014665391) ^ 103000862670 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 1751014665391) ^ 103225530 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 1751014665391) ^ 8651130 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1791732796583 : Nat.Prime 1791732796583 := by
  apply lucas_primality 1791732796583 (5 : ZMod 1791732796583)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (13371140273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (13371140273, 1)] : List FactorBlock).map factorBlockValue).prod) = 1791732796583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_67
      · exact prime_oneHundredFortyNineEQ_13371140273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1791732796583) ^ 895866398291 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1791732796583) ^ 26742280546 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1791732796583) ^ 134 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1856647861639 : Nat.Prime 1856647861639 := by
  apply lucas_primality 1856647861639 (3 : ZMod 1856647861639)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (4618527019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (4618527019, 1)] : List FactorBlock).map factorBlockValue).prod) = 1856647861639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_67
      · exact prime_oneHundredFortyNineEQ_4618527019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1856647861639) ^ 928323930819 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1856647861639) ^ 618882620546 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1856647861639) ^ 27711162114 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1856647861639) ^ 402 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2046087675283 : Nat.Prime 2046087675283 := by
  apply lucas_primality 2046087675283 (3 : ZMod 2046087675283)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (2865669013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (2865669013, 1)] : List FactorBlock).map factorBlockValue).prod) = 2046087675283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_2865669013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2046087675283) ^ 1023043837641 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2046087675283) ^ 682029225094 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2046087675283) ^ 292298239326 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2046087675283) ^ 120358098546 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2046087675283) ^ 714 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2184821879533 : Nat.Prime 2184821879533 := by
  apply lucas_primality 2184821879533 (2 : ZMod 2184821879533)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1783, 1), (1871, 1), (54577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1783, 1), (1871, 1), (54577, 1)] : List FactorBlock).map factorBlockValue).prod) = 2184821879533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_1783
      · exact prime_oneHundredFortyNineEQ_1871
      · exact prime_oneHundredFortyNineEQ_54577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2184821879533) ^ 1092410939766 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2184821879533) ^ 728273959844 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2184821879533) ^ 1225362804 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2184821879533) ^ 1167729492 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2184821879533) ^ 40031916 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2236057518949 : Nat.Prime 2236057518949 := by
  apply lucas_primality 2236057518949 (6 : ZMod 2236057518949)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (31, 1), (373, 1), (577, 1), (2539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (31, 1), (373, 1), (577, 1), (2539, 1)] : List FactorBlock).map factorBlockValue).prod) = 2236057518949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_31
      · exact prime_oneHundredFortyNineEQ_373
      · exact prime_oneHundredFortyNineEQ_577
      · exact prime_oneHundredFortyNineEQ_2539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2236057518949) ^ 1118028759474 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 2236057518949) ^ 745352506316 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 2236057518949) ^ 203277956268 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 2236057518949) ^ 72130887708 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 2236057518949) ^ 5994792276 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 2236057518949) ^ 3875316324 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 2236057518949) ^ 880684332 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2306115110149 : Nat.Prime 2306115110149 := by
  apply lucas_primality 2306115110149 (2 : ZMod 2306115110149)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (2159283811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (2159283811, 1)] : List FactorBlock).map factorBlockValue).prod) = 2306115110149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_89
      · exact prime_oneHundredFortyNineEQ_2159283811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2306115110149) ^ 1153057555074 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306115110149) ^ 768705036716 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306115110149) ^ 25911405732 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2306115110149) ^ 1068 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2754557430659 : Nat.Prime 2754557430659 := by
  apply lucas_primality 2754557430659 (6 : ZMod 2754557430659)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (125207155939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (125207155939, 1)] : List FactorBlock).map factorBlockValue).prod) = 2754557430659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_125207155939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 2754557430659) ^ 1377278715329 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 2754557430659) ^ 250414311878 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 2754557430659) ^ 22 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2910859769501 : Nat.Prime 2910859769501 := by
  apply lucas_primality 2910859769501 (2 : ZMod 2910859769501)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (109, 1), (53410271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (109, 1), (53410271, 1)] : List FactorBlock).map factorBlockValue).prod) = 2910859769501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_109
      · exact prime_oneHundredFortyNineEQ_53410271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2910859769501) ^ 1455429884750 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2910859769501) ^ 582171953900 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2910859769501) ^ 26705135500 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2910859769501) ^ 54500 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_3195195393697 : Nat.Prime 3195195393697 := by
  apply lucas_primality 3195195393697 (7 : ZMod 3195195393697)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (67, 1), (127, 1), (3911539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (67, 1), (127, 1), (3911539, 1)] : List FactorBlock).map factorBlockValue).prod) = 3195195393697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_67
      · exact prime_oneHundredFortyNineEQ_127
      · exact prime_oneHundredFortyNineEQ_3911539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3195195393697) ^ 1597597696848 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3195195393697) ^ 1065065131232 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3195195393697) ^ 47689483488 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3195195393697) ^ 25159018848 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3195195393697) ^ 816864 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_3409421658421 : Nat.Prime 3409421658421 := by
  apply lucas_primality 3409421658421 (2 : ZMod 3409421658421)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (31, 1), (96474863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (31, 1), (96474863, 1)] : List FactorBlock).map factorBlockValue).prod) = 3409421658421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_31
      · exact prime_oneHundredFortyNineEQ_96474863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3409421658421) ^ 1704710829210 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3409421658421) ^ 1136473886140 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3409421658421) ^ 681884331684 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3409421658421) ^ 179443245180 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3409421658421) ^ 109981343820 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3409421658421) ^ 35340 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_4531104717001 : Nat.Prime 4531104717001 := by
  apply lucas_primality 4531104717001 (17 : ZMod 4531104717001)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (22727, 1), (66457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (22727, 1), (66457, 1)] : List FactorBlock).map factorBlockValue).prod) = 4531104717001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_22727
      · exact prime_oneHundredFortyNineEQ_66457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 4531104717001) ^ 2265552358500 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 4531104717001) ^ 1510368239000 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 4531104717001) ^ 906220943400 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 4531104717001) ^ 199371000 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 4531104717001) ^ 68181000 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_5408190439403 : Nat.Prime 5408190439403 := by
  apply lucas_primality 5408190439403 (2 : ZMod 5408190439403)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2749, 1), (983665049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2749, 1), (983665049, 1)] : List FactorBlock).map factorBlockValue).prod) = 5408190439403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_2749
      · exact prime_oneHundredFortyNineEQ_983665049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5408190439403) ^ 2704095219701 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5408190439403) ^ 1967330098 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5408190439403) ^ 5498 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_6375165986363 : Nat.Prime 6375165986363 := by
  apply lucas_primality 6375165986363 (2 : ZMod 6375165986363)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (367, 1), (19577, 1), (443659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (367, 1), (19577, 1), (443659, 1)] : List FactorBlock).map factorBlockValue).prod) = 6375165986363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_367
      · exact prime_oneHundredFortyNineEQ_19577
      · exact prime_oneHundredFortyNineEQ_443659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6375165986363) ^ 3187582993181 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6375165986363) ^ 17371024486 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6375165986363) ^ 325645706 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6375165986363) ^ 14369518 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_7364144433817 : Nat.Prime 7364144433817 := by
  apply lucas_primality 7364144433817 (5 : ZMod 7364144433817)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (367, 1), (278691509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (367, 1), (278691509, 1)] : List FactorBlock).map factorBlockValue).prod) = 7364144433817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_367
      · exact prime_oneHundredFortyNineEQ_278691509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7364144433817) ^ 3682072216908 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 7364144433817) ^ 2454714811272 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 7364144433817) ^ 20065788648 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 7364144433817) ^ 26424 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_7668340868953 : Nat.Prime 7668340868953 := by
  apply lucas_primality 7668340868953 (10 : ZMod 7668340868953)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (34651, 1), (1024547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (34651, 1), (1024547, 1)] : List FactorBlock).map factorBlockValue).prod) = 7668340868953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_34651
      · exact prime_oneHundredFortyNineEQ_1024547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 7668340868953) ^ 3834170434476 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 7668340868953) ^ 2556113622984 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 7668340868953) ^ 221302152 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 7668340868953) ^ 7484616 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_8137708015631 : Nat.Prime 8137708015631 := by
  apply lucas_primality 8137708015631 (17 : ZMod 8137708015631)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (436957, 1), (1862359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (436957, 1), (1862359, 1)] : List FactorBlock).map factorBlockValue).prod) = 8137708015631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_436957
      · exact prime_oneHundredFortyNineEQ_1862359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 8137708015631) ^ 4068854007815 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 8137708015631) ^ 1627541603126 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 8137708015631) ^ 18623590 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 8137708015631) ^ 4369570 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_8571646159291 : Nat.Prime 8571646159291 := by
  apply lucas_primality 8571646159291 (3 : ZMod 8571646159291)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (5, 1), (391936267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (5, 1), (391936267, 1)] : List FactorBlock).map factorBlockValue).prod) = 8571646159291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_391936267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8571646159291) ^ 4285823079645 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 8571646159291) ^ 2857215386430 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 8571646159291) ^ 1714329231858 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 8571646159291) ^ 21870 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_8660455786187 : Nat.Prime 8660455786187 := by
  apply lucas_primality 8660455786187 (2 : ZMod 8660455786187)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (13127, 1), (19404227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (13127, 1), (19404227, 1)] : List FactorBlock).map factorBlockValue).prod) = 8660455786187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_13127
      · exact prime_oneHundredFortyNineEQ_19404227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8660455786187) ^ 4330227893093 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8660455786187) ^ 509438575658 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8660455786187) ^ 659743718 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 8660455786187) ^ 446318 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_9640812979727 : Nat.Prime 9640812979727 := by
  apply lucas_primality 9640812979727 (5 : ZMod 9640812979727)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (4813, 1), (14106181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (4813, 1), (14106181, 1)] : List FactorBlock).map factorBlockValue).prod) = 9640812979727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_71
      · exact prime_oneHundredFortyNineEQ_4813
      · exact prime_oneHundredFortyNineEQ_14106181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9640812979727) ^ 4820406489863 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 9640812979727) ^ 135786098306 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 9640812979727) ^ 2003077702 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 9640812979727) ^ 683446 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_10404370135283 : Nat.Prime 10404370135283 := by
  apply lucas_primality 10404370135283 (2 : ZMod 10404370135283)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (347, 1), (1489, 1), (58199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (347, 1), (1489, 1), (58199, 1)] : List FactorBlock).map factorBlockValue).prod) = 10404370135283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_173
      · exact prime_oneHundredFortyNineEQ_347
      · exact prime_oneHundredFortyNineEQ_1489
      · exact prime_oneHundredFortyNineEQ_58199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10404370135283) ^ 5202185067641 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10404370135283) ^ 60140867834 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10404370135283) ^ 29983775606 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10404370135283) ^ 6987488338 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10404370135283) ^ 178772318 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_10616222279581 : Nat.Prime 10616222279581 := by
  apply lucas_primality 10616222279581 (2 : ZMod 10616222279581)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (73, 1), (5987, 1), (404843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (73, 1), (5987, 1), (404843, 1)] : List FactorBlock).map factorBlockValue).prod) = 10616222279581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_73
      · exact prime_oneHundredFortyNineEQ_5987
      · exact prime_oneHundredFortyNineEQ_404843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10616222279581) ^ 5308111139790 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10616222279581) ^ 3538740759860 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10616222279581) ^ 2123244455916 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10616222279581) ^ 145427702460 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10616222279581) ^ 1773212340 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 10616222279581) ^ 26223060 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_11790155030987 : Nat.Prime 11790155030987 := by
  apply lucas_primality 11790155030987 (2 : ZMod 11790155030987)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (10691, 1), (19013987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (10691, 1), (19013987, 1)] : List FactorBlock).map factorBlockValue).prod) = 11790155030987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_29
      · exact prime_oneHundredFortyNineEQ_10691
      · exact prime_oneHundredFortyNineEQ_19013987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11790155030987) ^ 5895077515493 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11790155030987) ^ 406557070034 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11790155030987) ^ 1102811246 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11790155030987) ^ 620078 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_14850811348649 : Nat.Prime 14850811348649 := by
  apply lucas_primality 14850811348649 (3 : ZMod 14850811348649)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (15341747261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (15341747261, 1)] : List FactorBlock).map factorBlockValue).prod) = 14850811348649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_15341747261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14850811348649) ^ 7425405674324 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14850811348649) ^ 1350073758968 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14850811348649) ^ 968 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_16668513893377 : Nat.Prime 16668513893377 := by
  apply lucas_primality 16668513893377 (5 : ZMod 16668513893377)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 2), (1808649511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 2), (1808649511, 1)] : List FactorBlock).map factorBlockValue).prod) = 16668513893377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_1808649511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 16668513893377) ^ 8334256946688 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 16668513893377) ^ 5556171297792 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 16668513893377) ^ 9216 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_19372183061507 : Nat.Prime 19372183061507 := by
  apply lucas_primality 19372183061507 (2 : ZMod 19372183061507)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1447, 1), (7109, 1), (85601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1447, 1), (7109, 1), (85601, 1)] : List FactorBlock).map factorBlockValue).prod) = 19372183061507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_1447
      · exact prime_oneHundredFortyNineEQ_7109
      · exact prime_oneHundredFortyNineEQ_85601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19372183061507) ^ 9686091530753 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19372183061507) ^ 1761107551046 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19372183061507) ^ 13387825198 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19372183061507) ^ 2725022234 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19372183061507) ^ 226307906 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_21848218795331 : Nat.Prime 21848218795331 := by
  apply lucas_primality 21848218795331 (2 : ZMod 21848218795331)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2184821879533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2184821879533, 1)] : List FactorBlock).map factorBlockValue).prod) = 21848218795331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_2184821879533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21848218795331) ^ 10924109397665 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 21848218795331) ^ 4369643759066 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 21848218795331) ^ 10 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_29456577735269 : Nat.Prime 29456577735269 := by
  apply lucas_primality 29456577735269 (2 : ZMod 29456577735269)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7364144433817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7364144433817, 1)] : List FactorBlock).map factorBlockValue).prod) = 29456577735269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7364144433817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 29456577735269) ^ 14728288867634 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 29456577735269) ^ 4 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_30668088350909 : Nat.Prime 30668088350909 := by
  apply lucas_primality 30668088350909 (2 : ZMod 30668088350909)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (164743, 1), (46539289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (164743, 1), (46539289, 1)] : List FactorBlock).map factorBlockValue).prod) = 30668088350909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_164743
      · exact prime_oneHundredFortyNineEQ_46539289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30668088350909) ^ 15334044175454 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 30668088350909) ^ 186157156 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 30668088350909) ^ 658972 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_51049747255103 : Nat.Prime 51049747255103 := by
  apply lucas_primality 51049747255103 (5 : ZMod 51049747255103)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (77969, 1), (327372079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (77969, 1), (327372079, 1)] : List FactorBlock).map factorBlockValue).prod) = 51049747255103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_77969
      · exact prime_oneHundredFortyNineEQ_327372079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 51049747255103) ^ 25524873627551 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 51049747255103) ^ 654744158 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 51049747255103) ^ 155938 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_59554571844029 : Nat.Prime 59554571844029 := by
  apply lucas_primality 59554571844029 (2 : ZMod 59554571844029)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (857, 1), (17372978951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (857, 1), (17372978951, 1)] : List FactorBlock).map factorBlockValue).prod) = 59554571844029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_857
      · exact prime_oneHundredFortyNineEQ_17372978951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59554571844029) ^ 29777285922014 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 59554571844029) ^ 69491915804 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 59554571844029) ^ 3428 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_64898285272837 : Nat.Prime 64898285272837 := by
  apply lucas_primality 64898285272837 (2 : ZMod 64898285272837)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5408190439403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5408190439403, 1)] : List FactorBlock).map factorBlockValue).prod) = 64898285272837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5408190439403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 64898285272837) ^ 32449142636418 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 64898285272837) ^ 21632761757612 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 64898285272837) ^ 12 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_66674055573509 : Nat.Prime 66674055573509 := by
  apply lucas_primality 66674055573509 (2 : ZMod 66674055573509)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16668513893377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16668513893377, 1)] : List FactorBlock).map factorBlockValue).prod) = 66674055573509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_16668513893377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 66674055573509) ^ 33337027786754 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 66674055573509) ^ 4 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_70415511541759 : Nat.Prime 70415511541759 := by
  apply lucas_primality 70415511541759 (3 : ZMod 70415511541759)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (877, 1), (23909, 1), (62189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (877, 1), (23909, 1), (62189, 1)] : List FactorBlock).map factorBlockValue).prod) = 70415511541759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_877
      · exact prime_oneHundredFortyNineEQ_23909
      · exact prime_oneHundredFortyNineEQ_62189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 70415511541759) ^ 35207755770879 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 70415511541759) ^ 23471837180586 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 70415511541759) ^ 80291347254 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 70415511541759) ^ 2945146662 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 70415511541759) ^ 1132282422 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_112732128070909 : Nat.Prime 112732128070909 := by
  apply lucas_primality 112732128070909 (10 : ZMod 112732128070909)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2267, 1), (7103, 1), (583409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2267, 1), (7103, 1), (583409, 1)] : List FactorBlock).map factorBlockValue).prod) = 112732128070909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_2267
      · exact prime_oneHundredFortyNineEQ_7103
      · exact prime_oneHundredFortyNineEQ_583409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 112732128070909) ^ 56366064035454 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 112732128070909) ^ 37577376023636 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 112732128070909) ^ 49727449524 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 112732128070909) ^ 15871058436 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 112732128070909) ^ 193230012 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_137381186456993 : Nat.Prime 137381186456993 := by
  apply lucas_primality 137381186456993 (3 : ZMod 137381186456993)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (31, 1), (883, 1), (919, 1), (10039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (31, 1), (883, 1), (919, 1), (10039, 1)] : List FactorBlock).map factorBlockValue).prod) = 137381186456993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_31
      · exact prime_oneHundredFortyNineEQ_883
      · exact prime_oneHundredFortyNineEQ_919
      · exact prime_oneHundredFortyNineEQ_10039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 137381186456993) ^ 68690593228496 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 137381186456993) ^ 8081246262176 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 137381186456993) ^ 4431651176032 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 137381186456993) ^ 155584582624 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 137381186456993) ^ 149489865568 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 137381186456993) ^ 13684748128 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_163177978944181 : Nat.Prime 163177978944181 := by
  apply lucas_primality 163177978944181 (2 : ZMod 163177978944181)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (37, 1), (71, 1), (151, 1), (6856039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (37, 1), (71, 1), (151, 1), (6856039, 1)] : List FactorBlock).map factorBlockValue).prod) = 163177978944181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_37
      · exact prime_oneHundredFortyNineEQ_71
      · exact prime_oneHundredFortyNineEQ_151
      · exact prime_oneHundredFortyNineEQ_6856039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 163177978944181) ^ 81588989472090 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 163177978944181) ^ 54392659648060 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 163177978944181) ^ 32635595788836 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 163177978944181) ^ 4410215647140 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 163177978944181) ^ 2298281393580 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 163177978944181) ^ 1080648867180 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 163177978944181) ^ 23800620 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_191337650196851 : Nat.Prime 191337650196851 := by
  apply lucas_primality 191337650196851 (2 : ZMod 191337650196851)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (34253, 1), (111720229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (34253, 1), (111720229, 1)] : List FactorBlock).map factorBlockValue).prod) = 191337650196851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_34253
      · exact prime_oneHundredFortyNineEQ_111720229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 191337650196851) ^ 95668825098425 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 191337650196851) ^ 38267530039370 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 191337650196851) ^ 5586011450 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 191337650196851) ^ 1712650 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_255149757193021 : Nat.Prime 255149757193021 := by
  apply lucas_primality 255149757193021 (7 : ZMod 255149757193021)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2539, 1), (1674870403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2539, 1), (1674870403, 1)] : List FactorBlock).map factorBlockValue).prod) = 255149757193021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_2539
      · exact prime_oneHundredFortyNineEQ_1674870403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 255149757193021) ^ 127574878596510 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 255149757193021) ^ 85049919064340 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 255149757193021) ^ 51029951438604 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 255149757193021) ^ 100492224180 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 255149757193021) ^ 152340 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_375342685832581 : Nat.Prime 375342685832581 := by
  apply lucas_primality 375342685832581 (6 : ZMod 375342685832581)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (389, 1), (3407, 1), (4720141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (389, 1), (3407, 1), (4720141, 1)] : List FactorBlock).map factorBlockValue).prod) = 375342685832581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_389
      · exact prime_oneHundredFortyNineEQ_3407
      · exact prime_oneHundredFortyNineEQ_4720141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 375342685832581) ^ 187671342916290 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 375342685832581) ^ 125114228610860 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 375342685832581) ^ 75068537166516 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 375342685832581) ^ 964891223220 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 375342685832581) ^ 110168090940 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 375342685832581) ^ 79519380 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_382675300393703 : Nat.Prime 382675300393703 := by
  apply lucas_primality 382675300393703 (5 : ZMod 382675300393703)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191337650196851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191337650196851, 1)] : List FactorBlock).map factorBlockValue).prod) = 382675300393703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_191337650196851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 382675300393703) ^ 191337650196851 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 382675300393703) ^ 2 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_617102271134213 : Nat.Prime 617102271134213 := by
  apply lucas_primality 617102271134213 (2 : ZMod 617102271134213)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (2910859769501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (2910859769501, 1)] : List FactorBlock).map factorBlockValue).prod) = 617102271134213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_53
      · exact prime_oneHundredFortyNineEQ_2910859769501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 617102271134213) ^ 308551135567106 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 617102271134213) ^ 11643439078004 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 617102271134213) ^ 212 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_643323783785027 : Nat.Prime 643323783785027 := by
  apply lucas_primality 643323783785027 (2 : ZMod 643323783785027)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (36451, 1), (8824501163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (36451, 1), (8824501163, 1)] : List FactorBlock).map factorBlockValue).prod) = 643323783785027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_36451
      · exact prime_oneHundredFortyNineEQ_8824501163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 643323783785027) ^ 321661891892513 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 643323783785027) ^ 17649002326 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 643323783785027) ^ 72902 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_917888031221633 : Nat.Prime 917888031221633 := by
  apply lucas_primality 917888031221633 (3 : ZMod 917888031221633)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (43, 1), (239, 1), (9199, 1), (75853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (43, 1), (239, 1), (9199, 1), (75853, 1)] : List FactorBlock).map factorBlockValue).prod) = 917888031221633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_43
      · exact prime_oneHundredFortyNineEQ_239
      · exact prime_oneHundredFortyNineEQ_9199
      · exact prime_oneHundredFortyNineEQ_75853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 917888031221633) ^ 458944015610816 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 917888031221633) ^ 21346233284224 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 917888031221633) ^ 3840535695488 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 917888031221633) ^ 99781283968 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 917888031221633) ^ 12100879744 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1063615488200429 : Nat.Prime 1063615488200429 := by
  apply lucas_primality 1063615488200429 (2 : ZMod 1063615488200429)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (233, 1), (224771, 1), (5077249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (233, 1), (224771, 1), (5077249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063615488200429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_233
      · exact prime_oneHundredFortyNineEQ_224771
      · exact prime_oneHundredFortyNineEQ_5077249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1063615488200429) ^ 531807744100214 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063615488200429) ^ 4564873339916 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063615488200429) ^ 4731996068 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063615488200429) ^ 209486572 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1376013697575679 : Nat.Prime 1376013697575679 := by
  apply lucas_primality 1376013697575679 (6 : ZMod 1376013697575679)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (17, 1), (971, 1), (94511797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (17, 1), (971, 1), (94511797, 1)] : List FactorBlock).map factorBlockValue).prod) = 1376013697575679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_971
      · exact prime_oneHundredFortyNineEQ_94511797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1376013697575679) ^ 688006848787839 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1376013697575679) ^ 458671232525226 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1376013697575679) ^ 196573385367954 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1376013697575679) ^ 80941982210334 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1376013697575679) ^ 1417109884218 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1376013697575679) ^ 14559174 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2081433011286961 : Nat.Prime 2081433011286961 := by
  apply lucas_primality 2081433011286961 (7 : ZMod 2081433011286961)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (149, 1), (173, 1), (293, 1), (382763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (149, 1), (173, 1), (293, 1), (382763, 1)] : List FactorBlock).map factorBlockValue).prod) = 2081433011286961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_149
      · exact prime_oneHundredFortyNineEQ_173
      · exact prime_oneHundredFortyNineEQ_293
      · exact prime_oneHundredFortyNineEQ_382763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2081433011286961) ^ 1040716505643480 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2081433011286961) ^ 693811003762320 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2081433011286961) ^ 416286602257392 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2081433011286961) ^ 13969349069040 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2081433011286961) ^ 12031404689520 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2081433011286961) ^ 7103866932720 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2081433011286961) ^ 5437915920 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2403263143363931 : Nat.Prime 2403263143363931 := by
  apply lucas_primality 2403263143363931 (2 : ZMod 2403263143363931)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (99713, 1), (2410180361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (99713, 1), (2410180361, 1)] : List FactorBlock).map factorBlockValue).prod) = 2403263143363931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_99713
      · exact prime_oneHundredFortyNineEQ_2410180361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2403263143363931) ^ 1201631571681965 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2403263143363931) ^ 480652628672786 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2403263143363931) ^ 24101803610 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2403263143363931) ^ 997130 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2790147475023173 : Nat.Prime 2790147475023173 := by
  apply lucas_primality 2790147475023173 (2 : ZMod 2790147475023173)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (31, 1), (22369, 1), (91446317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (31, 1), (22369, 1), (91446317, 1)] : List FactorBlock).map factorBlockValue).prod) = 2790147475023173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_31
      · exact prime_oneHundredFortyNineEQ_22369
      · exact prime_oneHundredFortyNineEQ_91446317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2790147475023173) ^ 1395073737511586 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2790147475023173) ^ 253649770456652 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2790147475023173) ^ 90004757258812 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2790147475023173) ^ 124732776388 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2790147475023173) ^ 30511316 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2836674024299641 : Nat.Prime 2836674024299641 := by
  apply lucas_primality 2836674024299641 (13 : ZMod 2836674024299641)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 2), (53, 1), (15391, 1), (197137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 2), (53, 1), (15391, 1), (197137, 1)] : List FactorBlock).map factorBlockValue).prod) = 2836674024299641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_53
      · exact prime_oneHundredFortyNineEQ_15391
      · exact prime_oneHundredFortyNineEQ_197137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2836674024299641) ^ 1418337012149820 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2836674024299641) ^ 945558008099880 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2836674024299641) ^ 567334804859928 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2836674024299641) ^ 405239146328520 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2836674024299641) ^ 53522151401880 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2836674024299641) ^ 184307324040 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (13 : ZMod 2836674024299641) ^ 14389353720 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_3039888598934053 : Nat.Prime 3039888598934053 := by
  apply lucas_primality 3039888598934053 (2 : ZMod 3039888598934053)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10651, 1), (15307, 1), (1553803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10651, 1), (15307, 1), (1553803, 1)] : List FactorBlock).map factorBlockValue).prod) = 3039888598934053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_10651
      · exact prime_oneHundredFortyNineEQ_15307
      · exact prime_oneHundredFortyNineEQ_1553803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3039888598934053) ^ 1519944299467026 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3039888598934053) ^ 1013296199644684 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3039888598934053) ^ 285408750252 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3039888598934053) ^ 198594669036 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3039888598934053) ^ 1956418284 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_4397208079293737 : Nat.Prime 4397208079293737 := by
  apply lucas_primality 4397208079293737 (5 : ZMod 4397208079293737)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (59, 1), (335449, 1), (3967441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (59, 1), (335449, 1), (3967441, 1)] : List FactorBlock).map factorBlockValue).prod) = 4397208079293737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_59
      · exact prime_oneHundredFortyNineEQ_335449
      · exact prime_oneHundredFortyNineEQ_3967441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4397208079293737) ^ 2198604039646868 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4397208079293737) ^ 628172582756248 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4397208079293737) ^ 74528950496504 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4397208079293737) ^ 13108425064 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4397208079293737) ^ 1108323496 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_4806526286727863 : Nat.Prime 4806526286727863 := by
  apply lucas_primality 4806526286727863 (5 : ZMod 4806526286727863)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2403263143363931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2403263143363931, 1)] : List FactorBlock).map factorBlockValue).prod) = 4806526286727863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_2403263143363931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4806526286727863) ^ 2403263143363931 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4806526286727863) ^ 2 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_6123638508128087 : Nat.Prime 6123638508128087 := by
  apply lucas_primality 6123638508128087 (5 : ZMod 6123638508128087)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1723, 1), (161548000531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1723, 1), (161548000531, 1)] : List FactorBlock).map factorBlockValue).prod) = 6123638508128087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_1723
      · exact prime_oneHundredFortyNineEQ_161548000531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6123638508128087) ^ 3061819254064043 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6123638508128087) ^ 556694409829826 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6123638508128087) ^ 3554056011682 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6123638508128087) ^ 37906 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_7371075504613399 : Nat.Prime 7371075504613399 := by
  apply lucas_primality 7371075504613399 (15 : ZMod 7371075504613399)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (61, 1), (1229, 1), (7043, 1), (80231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (61, 1), (1229, 1), (7043, 1), (80231, 1)] : List FactorBlock).map factorBlockValue).prod) = 7371075504613399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_29
      · exact prime_oneHundredFortyNineEQ_61
      · exact prime_oneHundredFortyNineEQ_1229
      · exact prime_oneHundredFortyNineEQ_7043
      · exact prime_oneHundredFortyNineEQ_80231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 7371075504613399) ^ 3685537752306699 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (15 : ZMod 7371075504613399) ^ 2457025168204466 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (15 : ZMod 7371075504613399) ^ 254175017400462 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (15 : ZMod 7371075504613399) ^ 120837303354318 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (15 : ZMod 7371075504613399) ^ 5997620426862 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (15 : ZMod 7371075504613399) ^ 1046581783986 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (15 : ZMod 7371075504613399) ^ 91873160058 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_7635633197786749 : Nat.Prime 7635633197786749 := by
  apply lucas_primality 7635633197786749 (2 : ZMod 7635633197786749)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (11, 1), (2754557430659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (11, 1), (2754557430659, 1)] : List FactorBlock).map factorBlockValue).prod) = 7635633197786749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_2754557430659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7635633197786749) ^ 3817816598893374 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7635633197786749) ^ 2545211065928916 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7635633197786749) ^ 1090804742540964 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7635633197786749) ^ 694148472526068 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7635633197786749) ^ 2772 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_8071279613947871 : Nat.Prime 8071279613947871 := by
  apply lucas_primality 8071279613947871 (23 : ZMod 8071279613947871)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (29123, 1), (522914173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (29123, 1), (522914173, 1)] : List FactorBlock).map factorBlockValue).prod) = 8071279613947871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_53
      · exact prime_oneHundredFortyNineEQ_29123
      · exact prime_oneHundredFortyNineEQ_522914173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 8071279613947871) ^ 4035639806973935 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (23 : ZMod 8071279613947871) ^ 1614255922789574 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (23 : ZMod 8071279613947871) ^ 152288294602790 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (23 : ZMod 8071279613947871) ^ 277144511690 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (23 : ZMod 8071279613947871) ^ 15435190 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_9006532972990379 : Nat.Prime 9006532972990379 := by
  apply lucas_primality 9006532972990379 (2 : ZMod 9006532972990379)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (643323783785027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (643323783785027, 1)] : List FactorBlock).map factorBlockValue).prod) = 9006532972990379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_643323783785027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9006532972990379) ^ 4503266486495189 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9006532972990379) ^ 1286647567570054 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9006532972990379) ^ 14 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_9856146777399383 : Nat.Prime 9856146777399383 := by
  apply lucas_primality 9856146777399383 (5 : ZMod 9856146777399383)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (11519, 1), (9949332223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (11519, 1), (9949332223, 1)] : List FactorBlock).map factorBlockValue).prod) = 9856146777399383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_43
      · exact prime_oneHundredFortyNineEQ_11519
      · exact prime_oneHundredFortyNineEQ_9949332223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9856146777399383) ^ 4928073388699691 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 9856146777399383) ^ 229212715753474 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 9856146777399383) ^ 855642571178 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 9856146777399383) ^ 990634 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_10170236421752969 : Nat.Prime 10170236421752969 := by
  apply lucas_primality 10170236421752969 (3 : ZMod 10170236421752969)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (2683, 1), (91691, 1), (469787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (2683, 1), (91691, 1), (469787, 1)] : List FactorBlock).map factorBlockValue).prod) = 10170236421752969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_2683
      · exact prime_oneHundredFortyNineEQ_91691
      · exact prime_oneHundredFortyNineEQ_469787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10170236421752969) ^ 5085118210876484 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 10170236421752969) ^ 924566947432088 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 10170236421752969) ^ 3790621103896 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 10170236421752969) ^ 110918589848 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 10170236421752969) ^ 21648611864 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_12159554395736213 : Nat.Prime 12159554395736213 := by
  apply lucas_primality 12159554395736213 (2 : ZMod 12159554395736213)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3039888598934053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3039888598934053, 1)] : List FactorBlock).map factorBlockValue).prod) = 12159554395736213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3039888598934053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 12159554395736213) ^ 6079777197868106 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12159554395736213) ^ 4 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_14608170406875119 : Nat.Prime 14608170406875119 := by
  apply lucas_primality 14608170406875119 (7 : ZMod 14608170406875119)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (68541457, 1), (106564487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (68541457, 1), (106564487, 1)] : List FactorBlock).map factorBlockValue).prod) = 14608170406875119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_68541457
      · exact prime_oneHundredFortyNineEQ_106564487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 14608170406875119) ^ 7304085203437559 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 14608170406875119) ^ 213128974 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 14608170406875119) ^ 137082914 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_17860483003511471 : Nat.Prime 17860483003511471 := by
  apply lucas_primality 17860483003511471 (11 : ZMod 17860483003511471)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (255149757193021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (255149757193021, 1)] : List FactorBlock).map factorBlockValue).prod) = 17860483003511471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_255149757193021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 17860483003511471) ^ 8930241501755735 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 17860483003511471) ^ 3572096600702294 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 17860483003511471) ^ 2551497571930210 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 17860483003511471) ^ 70 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_25455764715292237 : Nat.Prime 25455764715292237 := by
  apply lucas_primality 25455764715292237 (14 : ZMod 25455764715292237)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (163177978944181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (163177978944181, 1)] : List FactorBlock).map factorBlockValue).prod) = 25455764715292237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_163177978944181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 25455764715292237) ^ 12727882357646118 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (14 : ZMod 25455764715292237) ^ 8485254905097412 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (14 : ZMod 25455764715292237) ^ 1958135747330172 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (14 : ZMod 25455764715292237) ^ 156 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_51950166075435371 : Nat.Prime 51950166075435371 := by
  apply lucas_primality 51950166075435371 (2 : ZMod 51950166075435371)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2539, 1), (2046087675283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2539, 1), (2046087675283, 1)] : List FactorBlock).map factorBlockValue).prod) = 51950166075435371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_2539
      · exact prime_oneHundredFortyNineEQ_2046087675283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51950166075435371) ^ 25975083037717685 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 51950166075435371) ^ 10390033215087074 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 51950166075435371) ^ 20460876752830 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 51950166075435371) ^ 25390 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_79436355108082487 : Nat.Prime 79436355108082487 := by
  apply lucas_primality 79436355108082487 (5 : ZMod 79436355108082487)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (197, 1), (997, 1), (1259, 1), (3735371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (197, 1), (997, 1), (1259, 1), (3735371, 1)] : List FactorBlock).map factorBlockValue).prod) = 79436355108082487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_43
      · exact prime_oneHundredFortyNineEQ_197
      · exact prime_oneHundredFortyNineEQ_997
      · exact prime_oneHundredFortyNineEQ_1259
      · exact prime_oneHundredFortyNineEQ_3735371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 79436355108082487) ^ 39718177554041243 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 79436355108082487) ^ 1847357095536802 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 79436355108082487) ^ 403230228975038 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 79436355108082487) ^ 79675381251838 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 79436355108082487) ^ 63094801515554 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 79436355108082487) ^ 21265988066 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_108078395675884549 : Nat.Prime 108078395675884549 := by
  apply lucas_primality 108078395675884549 (6 : ZMod 108078395675884549)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (9006532972990379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (9006532972990379, 1)] : List FactorBlock).map factorBlockValue).prod) = 108078395675884549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_9006532972990379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 108078395675884549) ^ 54039197837942274 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 108078395675884549) ^ 36026131891961516 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 108078395675884549) ^ 12 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_112155909222526097 : Nat.Prime 112155909222526097 := by
  apply lucas_primality 112155909222526097 (3 : ZMod 112155909222526097)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (461, 1), (691, 1), (1571, 1), (1621, 1), (8641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (461, 1), (691, 1), (1571, 1), (1621, 1), (8641, 1)] : List FactorBlock).map factorBlockValue).prod) = 112155909222526097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_461
      · exact prime_oneHundredFortyNineEQ_691
      · exact prime_oneHundredFortyNineEQ_1571
      · exact prime_oneHundredFortyNineEQ_1621
      · exact prime_oneHundredFortyNineEQ_8641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 112155909222526097) ^ 56077954611263048 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 112155909222526097) ^ 243288306339536 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 112155909222526097) ^ 162309564721456 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 112155909222526097) ^ 71391412617776 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 112155909222526097) ^ 69189333264976 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 112155909222526097) ^ 12979505754256 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_142725160666563929 : Nat.Prime 142725160666563929 := by
  apply lucas_primality 142725160666563929 (3 : ZMod 142725160666563929)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3100087, 1), (5754885293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3100087, 1), (5754885293, 1)] : List FactorBlock).map factorBlockValue).prod) = 142725160666563929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3100087
      · exact prime_oneHundredFortyNineEQ_5754885293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 142725160666563929) ^ 71362580333281964 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 142725160666563929) ^ 46039082344 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 142725160666563929) ^ 24800696 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_193876808079562057 : Nat.Prime 193876808079562057 := by
  apply lucas_primality 193876808079562057 (5 : ZMod 193876808079562057)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (139, 1), (19372183061507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (139, 1), (19372183061507, 1)] : List FactorBlock).map factorBlockValue).prod) = 193876808079562057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_139
      · exact prime_oneHundredFortyNineEQ_19372183061507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 193876808079562057) ^ 96938404039781028 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 193876808079562057) ^ 64625602693187352 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 193876808079562057) ^ 1394797180428504 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 193876808079562057) ^ 10008 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_234588548083103947 : Nat.Prime 234588548083103947 := by
  apply lucas_primality 234588548083103947 (3 : ZMod 234588548083103947)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1128577, 1), (11547902461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1128577, 1), (11547902461, 1)] : List FactorBlock).map factorBlockValue).prod) = 234588548083103947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_1128577
      · exact prime_oneHundredFortyNineEQ_11547902461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 234588548083103947) ^ 117294274041551973 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 234588548083103947) ^ 78196182694367982 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 234588548083103947) ^ 207862244298 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 234588548083103947) ^ 20314386 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_236059741949880451 : Nat.Prime 236059741949880451 := by
  apply lucas_primality 236059741949880451 (2 : ZMod 236059741949880451)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (19, 1), (23, 1), (4139, 1), (5419, 1), (22937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (19, 1), (23, 1), (4139, 1), (5419, 1), (22937, 1)] : List FactorBlock).map factorBlockValue).prod) = 236059741949880451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_23
      · exact prime_oneHundredFortyNineEQ_4139
      · exact prime_oneHundredFortyNineEQ_5419
      · exact prime_oneHundredFortyNineEQ_22937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 236059741949880451) ^ 118029870974940225 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 236059741949880451) ^ 78686580649960150 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 236059741949880451) ^ 47211948389976090 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 236059741949880451) ^ 33722820278554350 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 236059741949880451) ^ 12424196944730550 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 236059741949880451) ^ 10263467041299150 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 236059741949880451) ^ 57033037436550 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 236059741949880451) ^ 43561495100550 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 236059741949880451) ^ 10291657232850 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_285450321333127859 : Nat.Prime 285450321333127859 := by
  apply lucas_primality 285450321333127859 (2 : ZMod 285450321333127859)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (142725160666563929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (142725160666563929, 1)] : List FactorBlock).map factorBlockValue).prod) = 285450321333127859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_142725160666563929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 285450321333127859) ^ 142725160666563929 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 285450321333127859) ^ 2 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_524679489052132279 : Nat.Prime 524679489052132279 := by
  apply lucas_primality 524679489052132279 (3 : ZMod 524679489052132279)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1543, 1), (7425707, 1), (7632013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1543, 1), (7425707, 1), (7632013, 1)] : List FactorBlock).map factorBlockValue).prod) = 524679489052132279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_1543
      · exact prime_oneHundredFortyNineEQ_7425707
      · exact prime_oneHundredFortyNineEQ_7632013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 524679489052132279) ^ 262339744526066139 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 524679489052132279) ^ 174893163017377426 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 524679489052132279) ^ 340038554149146 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 524679489052132279) ^ 70657176354 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 524679489052132279) ^ 68747195406 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_673384203298663211 : Nat.Prime 673384203298663211 := by
  apply lucas_primality 673384203298663211 (2 : ZMod 673384203298663211)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11960527, 1), (5630054623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11960527, 1), (5630054623, 1)] : List FactorBlock).map factorBlockValue).prod) = 673384203298663211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_11960527
      · exact prime_oneHundredFortyNineEQ_5630054623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 673384203298663211) ^ 336692101649331605 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 673384203298663211) ^ 134676840659732642 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 673384203298663211) ^ 56300546230 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 673384203298663211) ^ 119605270 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_802530590118590059 : Nat.Prime 802530590118590059 := by
  apply lucas_primality 802530590118590059 (3 : ZMod 802530590118590059)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (12159554395736213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (12159554395736213, 1)] : List FactorBlock).map factorBlockValue).prod) = 802530590118590059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_12159554395736213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 802530590118590059) ^ 401265295059295029 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 802530590118590059) ^ 267510196706196686 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 802530590118590059) ^ 72957326374417278 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 802530590118590059) ^ 66 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1228296715311627473 : Nat.Prime 1228296715311627473 := by
  apply lucas_primality 1228296715311627473 (3 : ZMod 1228296715311627473)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (9829, 1), (159396173977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (9829, 1), (159396173977, 1)] : List FactorBlock).map factorBlockValue).prod) = 1228296715311627473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_9829
      · exact prime_oneHundredFortyNineEQ_159396173977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1228296715311627473) ^ 614148357655813736 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1228296715311627473) ^ 175470959330232496 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1228296715311627473) ^ 124966600397968 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1228296715311627473) ^ 7705936 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1724607866292494773 : Nat.Prime 1724607866292494773 := by
  apply lucas_primality 1724607866292494773 (2 : ZMod 1724607866292494773)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (61, 1), (9091, 1), (4392538859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (61, 1), (9091, 1), (4392538859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1724607866292494773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_59
      · exact prime_oneHundredFortyNineEQ_61
      · exact prime_oneHundredFortyNineEQ_9091
      · exact prime_oneHundredFortyNineEQ_4392538859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1724607866292494773) ^ 862303933146247386 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724607866292494773) ^ 574869288764164924 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724607866292494773) ^ 29230641801567708 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724607866292494773) ^ 28272260103155652 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724607866292494773) ^ 189704968242492 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724607866292494773) ^ 392622108 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2397662876258478599 : Nat.Prime 2397662876258478599 := by
  apply lucas_primality 2397662876258478599 (7 : ZMod 2397662876258478599)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (11, 1), (101, 1), (1601, 1), (9901, 1), (198463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (11, 1), (101, 1), (1601, 1), (9901, 1), (198463, 1)] : List FactorBlock).map factorBlockValue).prod) = 2397662876258478599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_101
      · exact prime_oneHundredFortyNineEQ_1601
      · exact prime_oneHundredFortyNineEQ_9901
      · exact prime_oneHundredFortyNineEQ_198463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2397662876258478599) ^ 1198831438129239299 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2397662876258478599) ^ 342523268036925514 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2397662876258478599) ^ 217969352387134418 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2397662876258478599) ^ 23739236398598798 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2397662876258478599) ^ 1497603295601798 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2397662876258478599) ^ 242163708338398 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2397662876258478599) ^ 12081158081146 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2900823119520630389 : Nat.Prime 2900823119520630389 := by
  apply lucas_primality 2900823119520630389 (2 : ZMod 2900823119520630389)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (919, 1), (112732128070909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (919, 1), (112732128070909, 1)] : List FactorBlock).map factorBlockValue).prod) = 2900823119520630389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_919
      · exact prime_oneHundredFortyNineEQ_112732128070909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2900823119520630389) ^ 1450411559760315194 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2900823119520630389) ^ 414403302788661484 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2900823119520630389) ^ 3156499585985452 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2900823119520630389) ^ 25732 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2921354454597852817 : Nat.Prime 2921354454597852817 := by
  apply lucas_primality 2921354454597852817 (5 : ZMod 2921354454597852817)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (37, 1), (7331, 1), (24930762629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (37, 1), (7331, 1), (24930762629, 1)] : List FactorBlock).map factorBlockValue).prod) = 2921354454597852817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_37
      · exact prime_oneHundredFortyNineEQ_7331
      · exact prime_oneHundredFortyNineEQ_24930762629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2921354454597852817) ^ 1460677227298926408 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2921354454597852817) ^ 973784818199284272 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2921354454597852817) ^ 78955525799941968 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2921354454597852817) ^ 398493309861936 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2921354454597852817) ^ 117178704 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_7255393330834666051 : Nat.Prime 7255393330834666051 := by
  apply lucas_primality 7255393330834666051 (3 : ZMod 7255393330834666051)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (4397208079293737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (4397208079293737, 1)] : List FactorBlock).map factorBlockValue).prod) = 7255393330834666051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_4397208079293737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7255393330834666051) ^ 3627696665417333025 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7255393330834666051) ^ 2418464443611555350 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7255393330834666051) ^ 1451078666166933210 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7255393330834666051) ^ 659581211894060550 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 7255393330834666051) ^ 1650 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_7283100358640709761 : Nat.Prime 7283100358640709761 := by
  apply lucas_primality 7283100358640709761 (6 : ZMod 7283100358640709761)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (67, 1), (97, 1), (1751014665391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (67, 1), (97, 1), (1751014665391, 1)] : List FactorBlock).map factorBlockValue).prod) = 7283100358640709761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_67
      · exact prime_oneHundredFortyNineEQ_97
      · exact prime_oneHundredFortyNineEQ_1751014665391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7283100358640709761) ^ 3641550179320354880 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 7283100358640709761) ^ 1456620071728141952 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 7283100358640709761) ^ 108702990427473280 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 7283100358640709761) ^ 75083508851966080 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 7283100358640709761) ^ 4159360 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_8091624855127131943 : Nat.Prime 8091624855127131943 := by
  apply lucas_primality 8091624855127131943 (5 : ZMod 8091624855127131943)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (53, 1), (199, 1), (1297, 1), (7583544071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (53, 1), (199, 1), (1297, 1), (7583544071, 1)] : List FactorBlock).map factorBlockValue).prod) = 8091624855127131943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_53
      · exact prime_oneHundredFortyNineEQ_199
      · exact prime_oneHundredFortyNineEQ_1297
      · exact prime_oneHundredFortyNineEQ_7583544071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8091624855127131943) ^ 4045812427563565971 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 8091624855127131943) ^ 2697208285042377314 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 8091624855127131943) ^ 622432681163625534 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 8091624855127131943) ^ 152672167077870414 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 8091624855127131943) ^ 40661431432799658 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 8091624855127131943) ^ 6238723866713286 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 8091624855127131943) ^ 1066997802 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_10516224017924241791 : Nat.Prime 10516224017924241791 := by
  apply lucas_primality 10516224017924241791 (11 : ZMod 10516224017924241791)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (1979, 1), (7451, 1), (32443, 1), (36037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (1979, 1), (7451, 1), (32443, 1), (36037, 1)] : List FactorBlock).map factorBlockValue).prod) = 10516224017924241791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_61
      · exact prime_oneHundredFortyNineEQ_1979
      · exact prime_oneHundredFortyNineEQ_7451
      · exact prime_oneHundredFortyNineEQ_32443
      · exact prime_oneHundredFortyNineEQ_36037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 10516224017924241791) ^ 5258112008962120895 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 10516224017924241791) ^ 2103244803584848358 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 10516224017924241791) ^ 172397115047938390 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 10516224017924241791) ^ 5313908043418010 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 10516224017924241791) ^ 1411384246131290 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 10516224017924241791) ^ 324144623429530 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 10516224017924241791) ^ 291817410381670 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_12987538391852097041 : Nat.Prime 12987538391852097041 := by
  apply lucas_primality 12987538391852097041 (3 : ZMod 12987538391852097041)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (17, 1), (29, 1), (2803, 1), (10680071377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (17, 1), (29, 1), (2803, 1), (10680071377, 1)] : List FactorBlock).map factorBlockValue).prod) = 12987538391852097041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_29
      · exact prime_oneHundredFortyNineEQ_2803
      · exact prime_oneHundredFortyNineEQ_10680071377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12987538391852097041) ^ 6493769195926048520 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12987538391852097041) ^ 2597507678370419408 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12987538391852097041) ^ 1180685308350190640 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12987538391852097041) ^ 763972846579535120 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12987538391852097041) ^ 447846151443175760 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12987538391852097041) ^ 4633442166197680 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12987538391852097041) ^ 1216053520 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_22867020332795161997 : Nat.Prime 22867020332795161997 := by
  apply lucas_primality 22867020332795161997 (2 : ZMod 22867020332795161997)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (7537, 1), (7726933, 1), (8923829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (7537, 1), (7726933, 1), (8923829, 1)] : List FactorBlock).map factorBlockValue).prod) = 22867020332795161997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_7537
      · exact prime_oneHundredFortyNineEQ_7726933
      · exact prime_oneHundredFortyNineEQ_8923829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22867020332795161997) ^ 11433510166397580998 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22867020332795161997) ^ 2078820030254105636 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22867020332795161997) ^ 3033968466604108 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22867020332795161997) ^ 2959391563612 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 22867020332795161997) ^ 2562467336924 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_26359294192761377879 : Nat.Prime 26359294192761377879 := by
  apply lucas_primality 26359294192761377879 (11 : ZMod 26359294192761377879)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (63103, 1), (326369, 1), (639948277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (63103, 1), (326369, 1), (639948277, 1)] : List FactorBlock).map factorBlockValue).prod) = 26359294192761377879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_63103
      · exact prime_oneHundredFortyNineEQ_326369
      · exact prime_oneHundredFortyNineEQ_639948277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 26359294192761377879) ^ 13179647096380688939 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 26359294192761377879) ^ 417718558432426 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 26359294192761377879) ^ 80765312247062 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 26359294192761377879) ^ 41189726014 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_38695436355550624219 : Nat.Prime 38695436355550624219 := by
  apply lucas_primality 38695436355550624219 (3 : ZMod 38695436355550624219)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (173, 1), (509, 1), (8137708015631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (173, 1), (509, 1), (8137708015631, 1)] : List FactorBlock).map factorBlockValue).prod) = 38695436355550624219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_173
      · exact prime_oneHundredFortyNineEQ_509
      · exact prime_oneHundredFortyNineEQ_8137708015631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38695436355550624219) ^ 19347718177775312109 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38695436355550624219) ^ 12898478785183541406 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38695436355550624219) ^ 223673042517633666 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38695436355550624219) ^ 76022468282024802 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38695436355550624219) ^ 4755078 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_58307346666610086937 : Nat.Prime 58307346666610086937 := by
  apply lucas_primality 58307346666610086937 (5 : ZMod 58307346666610086937)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (31, 1), (59, 1), (4507249, 1), (26791319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (31, 1), (59, 1), (4507249, 1), (26791319, 1)] : List FactorBlock).map factorBlockValue).prod) = 58307346666610086937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_31
      · exact prime_oneHundredFortyNineEQ_59
      · exact prime_oneHundredFortyNineEQ_4507249
      · exact prime_oneHundredFortyNineEQ_26791319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 58307346666610086937) ^ 29153673333305043468 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 58307346666610086937) ^ 19435782222203362312 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 58307346666610086937) ^ 5300667878782735176 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 58307346666610086937) ^ 1880882150535809256 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 58307346666610086937) ^ 988260112993391304 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 58307346666610086937) ^ 12936349127064 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 58307346666610086937) ^ 2176352223144 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_128084438127481043393 : Nat.Prime 128084438127481043393 := by
  apply lucas_primality 128084438127481043393 (3 : ZMod 128084438127481043393)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (137, 1), (14608170406875119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (137, 1), (14608170406875119, 1)] : List FactorBlock).map factorBlockValue).prod) = 128084438127481043393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_137
      · exact prime_oneHundredFortyNineEQ_14608170406875119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 128084438127481043393) ^ 64042219063740521696 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 128084438127481043393) ^ 934922906040007616 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 128084438127481043393) ^ 8768 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_305603269244442943567 : Nat.Prime 305603269244442943567 := by
  apply lucas_primality 305603269244442943567 (21 : ZMod 305603269244442943567)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (79, 1), (1465481, 1), (33842006903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (79, 1), (1465481, 1), (33842006903, 1)] : List FactorBlock).map factorBlockValue).prod) = 305603269244442943567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_79
      · exact prime_oneHundredFortyNineEQ_1465481
      · exact prime_oneHundredFortyNineEQ_33842006903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 305603269244442943567) ^ 152801634622221471783 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 305603269244442943567) ^ 101867756414814314522 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 305603269244442943567) ^ 23507943788034072582 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 305603269244442943567) ^ 3868395813220796754 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 305603269244442943567) ^ 208534446536286 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (21 : ZMod 305603269244442943567) ^ 9030293922 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_780794125616814757033 : Nat.Prime 780794125616814757033 := by
  apply lucas_primality 780794125616814757033 (5 : ZMod 780794125616814757033)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (1367, 1), (1358803, 1), (1347277111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (1367, 1), (1358803, 1), (1347277111, 1)] : List FactorBlock).map factorBlockValue).prod) = 780794125616814757033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_1367
      · exact prime_oneHundredFortyNineEQ_1358803
      · exact prime_oneHundredFortyNineEQ_1347277111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 780794125616814757033) ^ 390397062808407378516 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 780794125616814757033) ^ 260264708538938252344 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 780794125616814757033) ^ 60061086585908827464 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 780794125616814757033) ^ 571173464240537496 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 780794125616814757033) ^ 574619076949944 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 780794125616814757033) ^ 579534914712 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1555967601680743158659 : Nat.Prime 1555967601680743158659 := by
  apply lucas_primality 1555967601680743158659 (2 : ZMod 1555967601680743158659)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101453993, 1), (7668340868953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101453993, 1), (7668340868953, 1)] : List FactorBlock).map factorBlockValue).prod) = 1555967601680743158659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_101453993
      · exact prime_oneHundredFortyNineEQ_7668340868953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1555967601680743158659) ^ 777983800840371579329 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1555967601680743158659) ^ 15336681737906 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1555967601680743158659) ^ 202907986 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2824446868232487789623 : Nat.Prime 2824446868232487789623 := by
  apply lucas_primality 2824446868232487789623 (5 : ZMod 2824446868232487789623)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (31, 1), (2397662876258478599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (31, 1), (2397662876258478599, 1)] : List FactorBlock).map factorBlockValue).prod) = 2824446868232487789623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_31
      · exact prime_oneHundredFortyNineEQ_2397662876258478599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2824446868232487789623) ^ 1412223434116243894811 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2824446868232487789623) ^ 148655098328025673138 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2824446868232487789623) ^ 91111189297822186762 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2824446868232487789623) ^ 1178 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_4929979900654734645817 : Nat.Prime 4929979900654734645817 := by
  apply lucas_primality 4929979900654734645817 (5 : ZMod 4929979900654734645817)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (37, 1), (103811, 1), (106433, 1), (167490913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (37, 1), (103811, 1), (106433, 1), (167490913, 1)] : List FactorBlock).map factorBlockValue).prod) = 4929979900654734645817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_37
      · exact prime_oneHundredFortyNineEQ_103811
      · exact prime_oneHundredFortyNineEQ_106433
      · exact prime_oneHundredFortyNineEQ_167490913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4929979900654734645817) ^ 2464989950327367322908 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4929979900654734645817) ^ 1643326633551578215272 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4929979900654734645817) ^ 133242700017695530968 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4929979900654734645817) ^ 47489956754628456 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4929979900654734645817) ^ 46320031387396152 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4929979900654734645817) ^ 29434312658232 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_5291167189977644766341 : Nat.Prime 5291167189977644766341 := by
  apply lucas_primality 5291167189977644766341 (7 : ZMod 5291167189977644766341)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (17, 1), (3697, 1), (382675300393703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (17, 1), (3697, 1), (382675300393703, 1)] : List FactorBlock).map factorBlockValue).prod) = 5291167189977644766341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_3697
      · exact prime_oneHundredFortyNineEQ_382675300393703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5291167189977644766341) ^ 2645583594988822383170 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5291167189977644766341) ^ 1058233437995528953268 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5291167189977644766341) ^ 481015199088876796940 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5291167189977644766341) ^ 311245128822214398020 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5291167189977644766341) ^ 1431205623472449220 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 5291167189977644766341) ^ 13826780 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_5349693768399919635113 : Nat.Prime 5349693768399919635113 := by
  apply lucas_primality 5349693768399919635113 (3 : ZMod 5349693768399919635113)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (56041, 1), (917888031221633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (56041, 1), (917888031221633, 1)] : List FactorBlock).map factorBlockValue).prod) = 5349693768399919635113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_56041
      · exact prime_oneHundredFortyNineEQ_917888031221633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5349693768399919635113) ^ 2674846884199959817556 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5349693768399919635113) ^ 411514905261532279624 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5349693768399919635113) ^ 95460355247049832 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 5349693768399919635113) ^ 5828264 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_7685066287648862603581 : Nat.Prime 7685066287648862603581 := by
  apply lucas_primality 7685066287648862603581 (6 : ZMod 7685066287648862603581)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (128084438127481043393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (128084438127481043393, 1)] : List FactorBlock).map factorBlockValue).prod) = 7685066287648862603581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_128084438127481043393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 7685066287648862603581) ^ 3842533143824431301790 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 7685066287648862603581) ^ 2561688762549620867860 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 7685066287648862603581) ^ 1537013257529772520716 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 7685066287648862603581) ^ 60 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_8430118652521116083153 : Nat.Prime 8430118652521116083153 := by
  apply lucas_primality 8430118652521116083153 (3 : ZMod 8430118652521116083153)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (157, 1), (8941, 1), (375342685832581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (157, 1), (8941, 1), (375342685832581, 1)] : List FactorBlock).map factorBlockValue).prod) = 8430118652521116083153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_157
      · exact prime_oneHundredFortyNineEQ_8941
      · exact prime_oneHundredFortyNineEQ_375342685832581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8430118652521116083153) ^ 4215059326260558041576 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 8430118652521116083153) ^ 53695023264465707536 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 8430118652521116083153) ^ 942860826811443472 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 8430118652521116083153) ^ 22459792 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_20997732217507193530861 : Nat.Prime 20997732217507193530861 := by
  apply lucas_primality 20997732217507193530861 (2 : ZMod 20997732217507193530861)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (35507, 1), (9856146777399383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (35507, 1), (9856146777399383, 1)] : List FactorBlock).map factorBlockValue).prod) = 20997732217507193530861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_35507
      · exact prime_oneHundredFortyNineEQ_9856146777399383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20997732217507193530861) ^ 10498866108753596765430 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20997732217507193530861) ^ 6999244072502397843620 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20997732217507193530861) ^ 4199546443501438706172 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20997732217507193530861) ^ 591368806643962980 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 20997732217507193530861) ^ 2130420 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_26404857999587874791059 : Nat.Prime 26404857999587874791059 := by
  apply lucas_primality 26404857999587874791059 (3 : ZMod 26404857999587874791059)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22699, 1), (193876808079562057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22699, 1), (193876808079562057, 1)] : List FactorBlock).map factorBlockValue).prod) = 26404857999587874791059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_22699
      · exact prime_oneHundredFortyNineEQ_193876808079562057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26404857999587874791059) ^ 13202428999793937395529 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 26404857999587874791059) ^ 8801619333195958263686 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 26404857999587874791059) ^ 1163260848477372342 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 26404857999587874791059) ^ 136194 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_32009467358200684189091 : Nat.Prime 32009467358200684189091 := by
  apply lucas_primality 32009467358200684189091 (6 : ZMod 32009467358200684189091)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (91072727, 1), (3195195393697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (91072727, 1), (3195195393697, 1)] : List FactorBlock).map factorBlockValue).prod) = 32009467358200684189091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_91072727
      · exact prime_oneHundredFortyNineEQ_3195195393697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 32009467358200684189091) ^ 16004733679100342094545 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 32009467358200684189091) ^ 6401893471640136837818 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 32009467358200684189091) ^ 2909951578018244017190 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 32009467358200684189091) ^ 351471493306670 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 32009467358200684189091) ^ 10017999970 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_49042868434856887358437 : Nat.Prime 49042868434856887358437 := by
  apply lucas_primality 49042868434856887358437 (5 : ZMod 49042868434856887358437)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1103, 1), (290002327, 1), (12776668363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1103, 1), (290002327, 1), (12776668363, 1)] : List FactorBlock).map factorBlockValue).prod) = 49042868434856887358437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_1103
      · exact prime_oneHundredFortyNineEQ_290002327
      · exact prime_oneHundredFortyNineEQ_12776668363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 49042868434856887358437) ^ 24521434217428443679218 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 49042868434856887358437) ^ 16347622811618962452812 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 49042868434856887358437) ^ 44463162678927368412 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 49042868434856887358437) ^ 169111982452668 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 49042868434856887358437) ^ 3838470800172 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_51785184513905257338589 : Nat.Prime 51785184513905257338589 := by
  apply lucas_primality 51785184513905257338589 (10 : ZMod 51785184513905257338589)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (4931, 1), (17860483003511471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (4931, 1), (17860483003511471, 1)] : List FactorBlock).map factorBlockValue).prod) = 51785184513905257338589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_4931
      · exact prime_oneHundredFortyNineEQ_17860483003511471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 51785184513905257338589) ^ 25892592256952628669294 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 51785184513905257338589) ^ 17261728171301752446196 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 51785184513905257338589) ^ 7397883501986465334084 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 51785184513905257338589) ^ 10501964006064744948 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 51785184513905257338589) ^ 2899428 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_66670034675715783467693 : Nat.Prime 66670034675715783467693 := by
  apply lucas_primality 66670034675715783467693 (2 : ZMod 66670034675715783467693)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (373, 1), (79841, 1), (29456577735269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (373, 1), (79841, 1), (29456577735269, 1)] : List FactorBlock).map factorBlockValue).prod) = 66670034675715783467693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_19
      · exact prime_oneHundredFortyNineEQ_373
      · exact prime_oneHundredFortyNineEQ_79841
      · exact prime_oneHundredFortyNineEQ_29456577735269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66670034675715783467693) ^ 33335017337857891733846 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 66670034675715783467693) ^ 3508949193458725445668 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 66670034675715783467693) ^ 178740039345082529404 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 66670034675715783467693) ^ 835035065639405612 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 66670034675715783467693) ^ 2263332668 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_73107309965197450217089 : Nat.Prime 73107309965197450217089 := by
  apply lucas_primality 73107309965197450217089 (7 : ZMod 73107309965197450217089)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (11, 1), (23, 1), (1350469, 1), (557217104351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (11, 1), (23, 1), (1350469, 1), (557217104351, 1)] : List FactorBlock).map factorBlockValue).prod) = 73107309965197450217089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_23
      · exact prime_oneHundredFortyNineEQ_1350469
      · exact prime_oneHundredFortyNineEQ_557217104351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 73107309965197450217089) ^ 36553654982598725108544 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73107309965197450217089) ^ 24369103321732483405696 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73107309965197450217089) ^ 6646119087745222747008 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73107309965197450217089) ^ 3178578694139019574656 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73107309965197450217089) ^ 54134756121908352 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 73107309965197450217089) ^ 131200764288 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_73954684435994146732889 : Nat.Prime 73954684435994146732889 := by
  apply lucas_primality 73954684435994146732889 (3 : ZMod 73954684435994146732889)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (39161, 1), (236059741949880451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (39161, 1), (236059741949880451, 1)] : List FactorBlock).map factorBlockValue).prod) = 73954684435994146732889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_39161
      · exact prime_oneHundredFortyNineEQ_236059741949880451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 73954684435994146732889) ^ 36977342217997073366444 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73954684435994146732889) ^ 1888477935599043608 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73954684435994146732889) ^ 313288 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_97066460584059508897427 : Nat.Prime 97066460584059508897427 := by
  apply lucas_primality 97066460584059508897427 (2 : ZMod 97066460584059508897427)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (239818763, 1), (1856647861639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (239818763, 1), (1856647861639, 1)] : List FactorBlock).map factorBlockValue).prod) = 97066460584059508897427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_109
      · exact prime_oneHundredFortyNineEQ_239818763
      · exact prime_oneHundredFortyNineEQ_1856647861639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 97066460584059508897427) ^ 48533230292029754448713 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97066460584059508897427) ^ 890517987009720265114 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97066460584059508897427) ^ 404749233837302 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 97066460584059508897427) ^ 52280490334 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_421324226525204294852233 : Nat.Prime 421324226525204294852233 := by
  apply lucas_primality 421324226525204294852233 (5 : ZMod 421324226525204294852233)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 6), (2968854299, 1), (24333805499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 6), (2968854299, 1), (24333805499, 1)] : List FactorBlock).map factorBlockValue).prod) = 421324226525204294852233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_2968854299
      · exact prime_oneHundredFortyNineEQ_24333805499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 421324226525204294852233) ^ 210662113262602147426116 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 421324226525204294852233) ^ 140441408841734764950744 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 421324226525204294852233) ^ 141914753670168 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 421324226525204294852233) ^ 17314358271768 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_675412709128388097690673 : Nat.Prime 675412709128388097690673 := by
  apply lucas_primality 675412709128388097690673 (5 : ZMod 675412709128388097690673)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (17, 1), (739, 1), (6269, 1), (59554571844029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (17, 1), (739, 1), (6269, 1), (59554571844029, 1)] : List FactorBlock).map factorBlockValue).prod) = 675412709128388097690673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_739
      · exact prime_oneHundredFortyNineEQ_6269
      · exact prime_oneHundredFortyNineEQ_59554571844029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 675412709128388097690673) ^ 337706354564194048845336 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 675412709128388097690673) ^ 225137569709462699230224 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 675412709128388097690673) ^ 39730159360493417511216 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 675412709128388097690673) ^ 913954951459253176848 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 675412709128388097690673) ^ 107738508395021231088 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 675412709128388097690673) ^ 11341072368 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2167188693116979254209843 : Nat.Prime 2167188693116979254209843 := by
  apply lucas_primality 2167188693116979254209843 (2 : ZMod 2167188693116979254209843)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (7685066287648862603581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (7685066287648862603581, 1)] : List FactorBlock).map factorBlockValue).prod) = 2167188693116979254209843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_47
      · exact prime_oneHundredFortyNineEQ_7685066287648862603581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2167188693116979254209843) ^ 1083594346558489627104921 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167188693116979254209843) ^ 722396231038993084736614 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167188693116979254209843) ^ 46110397725893175621486 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167188693116979254209843) ^ 282 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_6566680300131236177558819 : Nat.Prime 6566680300131236177558819 := by
  apply lucas_primality 6566680300131236177558819 (2 : ZMod 6566680300131236177558819)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 2), (197, 1), (433, 1), (7635633197786749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 2), (197, 1), (433, 1), (7635633197786749, 1)] : List FactorBlock).map factorBlockValue).prod) = 6566680300131236177558819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_71
      · exact prime_oneHundredFortyNineEQ_197
      · exact prime_oneHundredFortyNineEQ_433
      · exact prime_oneHundredFortyNineEQ_7635633197786749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6566680300131236177558819) ^ 3283340150065618088779409 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6566680300131236177558819) ^ 92488454931425861655758 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6566680300131236177558819) ^ 33333402538737239479994 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6566680300131236177558819) ^ 15165543418316942673346 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6566680300131236177558819) ^ 860004682 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_9387570782377859936008147 : Nat.Prime 9387570782377859936008147 := by
  apply lucas_primality 9387570782377859936008147 (2 : ZMod 9387570782377859936008147)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9743, 1), (5365465817, 1), (29929663861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9743, 1), (5365465817, 1), (29929663861, 1)] : List FactorBlock).map factorBlockValue).prod) = 9387570782377859936008147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_9743
      · exact prime_oneHundredFortyNineEQ_5365465817
      · exact prime_oneHundredFortyNineEQ_29929663861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9387570782377859936008147) ^ 4693785391188929968004073 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9387570782377859936008147) ^ 3129190260792619978669382 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9387570782377859936008147) ^ 963519530162974436622 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9387570782377859936008147) ^ 1749628289986338 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 9387570782377859936008147) ^ 313654400730186 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_12415968827975792338539109 : Nat.Prime 12415968827975792338539109 := by
  apply lucas_primality 12415968827975792338539109 (2 : ZMod 12415968827975792338539109)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (45247, 1), (22867020332795161997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (45247, 1), (22867020332795161997, 1)] : List FactorBlock).map factorBlockValue).prod) = 12415968827975792338539109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_45247
      · exact prime_oneHundredFortyNineEQ_22867020332795161997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12415968827975792338539109) ^ 6207984413987896169269554 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12415968827975792338539109) ^ 4138656275991930779513036 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12415968827975792338539109) ^ 274404243993541943964 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12415968827975792338539109) ^ 542964 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_15024116480283201850677431 : Nat.Prime 15024116480283201850677431 := by
  apply lucas_primality 15024116480283201850677431 (17 : ZMod 15024116480283201850677431)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (41, 1), (239079433, 1), (11790155030987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (41, 1), (239079433, 1), (11790155030987, 1)] : List FactorBlock).map factorBlockValue).prod) = 15024116480283201850677431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_41
      · exact prime_oneHundredFortyNineEQ_239079433
      · exact prime_oneHundredFortyNineEQ_11790155030987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 15024116480283201850677431) ^ 7512058240141600925338715 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 15024116480283201850677431) ^ 3004823296056640370135486 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 15024116480283201850677431) ^ 1155701267714092450052110 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 15024116480283201850677431) ^ 366441865372761020748230 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 15024116480283201850677431) ^ 62841526315160710 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 15024116480283201850677431) ^ 1274293377890 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_27541864560869378001749981 : Nat.Prime 27541864560869378001749981 := by
  apply lucas_primality 27541864560869378001749981 (2 : ZMod 27541864560869378001749981)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (170616469, 1), (8071279613947871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (170616469, 1), (8071279613947871, 1)] : List FactorBlock).map factorBlockValue).prod) = 27541864560869378001749981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_170616469
      · exact prime_oneHundredFortyNineEQ_8071279613947871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27541864560869378001749981) ^ 13770932280434689000874990 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 27541864560869378001749981) ^ 5508372912173875600349996 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 27541864560869378001749981) ^ 161425592278957420 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 27541864560869378001749981) ^ 3412329380 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_51030638971993204431979397 : Nat.Prime 51030638971993204431979397 := by
  apply lucas_primality 51030638971993204431979397 (2 : ZMod 51030638971993204431979397)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (347, 1), (5737, 1), (24001, 1), (1208189562871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (347, 1), (5737, 1), (24001, 1), (1208189562871, 1)] : List FactorBlock).map factorBlockValue).prod) = 51030638971993204431979397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_347
      · exact prime_oneHundredFortyNineEQ_5737
      · exact prime_oneHundredFortyNineEQ_24001
      · exact prime_oneHundredFortyNineEQ_1208189562871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51030638971993204431979397) ^ 25515319485996602215989698 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 51030638971993204431979397) ^ 3925433767076400340921492 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 51030638971993204431979397) ^ 3001802292470188495998788 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 51030638971993204431979397) ^ 147062360149836324011468 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 51030638971993204431979397) ^ 8895004178489315745508 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 51030638971993204431979397) ^ 2126188032665022475396 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 51030638971993204431979397) ^ 42237278437276 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_108538364591078583918171829 : Nat.Prime 108538364591078583918171829 := by
  apply lucas_primality 108538364591078583918171829 (6 : ZMod 108538364591078583918171829)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (227, 1), (46958631121, 1), (121216768451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (227, 1), (46958631121, 1), (121216768451, 1)] : List FactorBlock).map factorBlockValue).prod) = 108538364591078583918171829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_227
      · exact prime_oneHundredFortyNineEQ_46958631121
      · exact prime_oneHundredFortyNineEQ_121216768451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 108538364591078583918171829) ^ 54269182295539291959085914 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 108538364591078583918171829) ^ 36179454863692861306057276 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 108538364591078583918171829) ^ 15505480655868369131167404 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 108538364591078583918171829) ^ 478142575291095083339964 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 108538364591078583918171829) ^ 2311361340823668 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 108538364591078583918171829) ^ 895407178215228 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_110029834935240813053836901 : Nat.Prime 110029834935240813053836901 := by
  apply lucas_primality 110029834935240813053836901 (10 : ZMod 110029834935240813053836901)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (151, 1), (169991, 1), (6123638508128087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (151, 1), (169991, 1), (6123638508128087, 1)] : List FactorBlock).map factorBlockValue).prod) = 110029834935240813053836901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_151
      · exact prime_oneHundredFortyNineEQ_169991
      · exact prime_oneHundredFortyNineEQ_6123638508128087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 110029834935240813053836901) ^ 55014917467620406526918450 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 110029834935240813053836901) ^ 22005966987048162610767380 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 110029834935240813053836901) ^ 15718547847891544721976700 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 110029834935240813053836901) ^ 728674403544641146051900 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 110029834935240813053836901) ^ 647268590309138795900 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (10 : ZMod 110029834935240813053836901) ^ 17968048700 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_271011947278954679537219813 : Nat.Prime 271011947278954679537219813 := by
  apply lucas_primality 271011947278954679537219813 (2 : ZMod 271011947278954679537219813)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (16931, 1), (2997813257, 1), (22625034401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (16931, 1), (2997813257, 1), (22625034401, 1)] : List FactorBlock).map factorBlockValue).prod) = 271011947278954679537219813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_59
      · exact prime_oneHundredFortyNineEQ_16931
      · exact prime_oneHundredFortyNineEQ_2997813257
      · exact prime_oneHundredFortyNineEQ_22625034401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 271011947278954679537219813) ^ 135505973639477339768609906 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 271011947278954679537219813) ^ 4593422835236519992156268 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 271011947278954679537219813) ^ 16006848223906129557452 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 271011947278954679537219813) ^ 90403211956626116 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 271011947278954679537219813) ^ 11978410396007012 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_328652548006195040483568803 : Nat.Prime 328652548006195040483568803 := by
  apply lucas_primality 328652548006195040483568803 (2 : ZMod 328652548006195040483568803)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (811, 1), (1103, 1), (38219, 1), (4806526286727863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (811, 1), (1103, 1), (38219, 1), (4806526286727863, 1)] : List FactorBlock).map factorBlockValue).prod) = 328652548006195040483568803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_811
      · exact prime_oneHundredFortyNineEQ_1103
      · exact prime_oneHundredFortyNineEQ_38219
      · exact prime_oneHundredFortyNineEQ_4806526286727863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 328652548006195040483568803) ^ 164326274003097520241784401 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 328652548006195040483568803) ^ 405243585704309544369382 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 328652548006195040483568803) ^ 297962418863277461907134 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 328652548006195040483568803) ^ 8599192757691070945958 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 328652548006195040483568803) ^ 68376313454 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_367761515096702592273889099 : Nat.Prime 367761515096702592273889099 := by
  apply lucas_primality 367761515096702592273889099 (2 : ZMod 367761515096702592273889099)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13313, 1), (69401, 1), (7371075504613399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13313, 1), (69401, 1), (7371075504613399, 1)] : List FactorBlock).map factorBlockValue).prod) = 367761515096702592273889099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_13313
      · exact prime_oneHundredFortyNineEQ_69401
      · exact prime_oneHundredFortyNineEQ_7371075504613399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 367761515096702592273889099) ^ 183880757548351296136944549 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 367761515096702592273889099) ^ 122587171698900864091296366 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 367761515096702592273889099) ^ 27624240599166423215946 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 367761515096702592273889099) ^ 5299080922417581767898 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 367761515096702592273889099) ^ 49892517702 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_927146135428002851048383571 : Nat.Prime 927146135428002851048383571 := by
  apply lucas_primality 927146135428002851048383571 (6 : ZMod 927146135428002851048383571)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (131, 1), (16501123, 1), (58795159, 1), (104213453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (131, 1), (16501123, 1), (58795159, 1), (104213453, 1)] : List FactorBlock).map factorBlockValue).prod) = 927146135428002851048383571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_131
      · exact prime_oneHundredFortyNineEQ_16501123
      · exact prime_oneHundredFortyNineEQ_58795159
      · exact prime_oneHundredFortyNineEQ_104213453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 927146135428002851048383571) ^ 463573067714001425524191785 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 927146135428002851048383571) ^ 185429227085600570209676714 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 927146135428002851048383571) ^ 132449447918286121578340510 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 927146135428002851048383571) ^ 7077451415480937794262470 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 927146135428002851048383571) ^ 56186850763308827590 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 927146135428002851048383571) ^ 15769089686924783230 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 927146135428002851048383571) ^ 8896606999750817690 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1012400952478853687926395853 : Nat.Prime 1012400952478853687926395853 := by
  apply lucas_primality 1012400952478853687926395853 (2 : ZMod 1012400952478853687926395853)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109, 1), (157, 1), (4929979900654734645817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109, 1), (157, 1), (4929979900654734645817, 1)] : List FactorBlock).map factorBlockValue).prod) = 1012400952478853687926395853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_109
      · exact prime_oneHundredFortyNineEQ_157
      · exact prime_oneHundredFortyNineEQ_4929979900654734645817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1012400952478853687926395853) ^ 506200476239426843963197926 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012400952478853687926395853) ^ 337466984159617895975465284 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012400952478853687926395853) ^ 9288082132833520072719228 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012400952478853687926395853) ^ 6448413710056392916728636 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012400952478853687926395853) ^ 205356 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1365564075436593346505371151 : Nat.Prime 1365564075436593346505371151 := by
  apply lucas_primality 1365564075436593346505371151 (11 : ZMod 1365564075436593346505371151)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (409623822547, 1), (66674055573509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (409623822547, 1), (66674055573509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1365564075436593346505371151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_409623822547
      · exact prime_oneHundredFortyNineEQ_66674055573509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1365564075436593346505371151) ^ 682782037718296673252685575 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1365564075436593346505371151) ^ 273112815087318669301074230 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1365564075436593346505371151) ^ 3333702778675450 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1365564075436593346505371151) ^ 20481191127350 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_1834976726367922309366592483 : Nat.Prime 1834976726367922309366592483 := by
  apply lucas_primality 1834976726367922309366592483 (2 : ZMod 1834976726367922309366592483)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (30449, 1), (53887, 1), (5118871, 1), (264496109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (30449, 1), (53887, 1), (5118871, 1), (264496109, 1)] : List FactorBlock).map factorBlockValue).prod) = 1834976726367922309366592483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_59
      · exact prime_oneHundredFortyNineEQ_30449
      · exact prime_oneHundredFortyNineEQ_53887
      · exact prime_oneHundredFortyNineEQ_5118871
      · exact prime_oneHundredFortyNineEQ_264496109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1834976726367922309366592483) ^ 917488363183961154683296241 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1834976726367922309366592483) ^ 262139532338274615623798926 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1834976726367922309366592483) ^ 31101300446913937446891398 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1834976726367922309366592483) ^ 60263940568423340975618 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1834976726367922309366592483) ^ 34052308095977180198686 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1834976726367922309366592483) ^ 358472937952123096942 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1834976726367922309366592483) ^ 6937632214347328298 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2174787231250870885175220721 : Nat.Prime 2174787231250870885175220721 := by
  apply lucas_primality 2174787231250870885175220721 (7 : ZMod 2174787231250870885175220721)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 2), (2341, 1), (8209, 1), (2790147475023173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 2), (2341, 1), (8209, 1), (2790147475023173, 1)] : List FactorBlock).map factorBlockValue).prod) = 2174787231250870885175220721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_13
      · exact prime_oneHundredFortyNineEQ_2341
      · exact prime_oneHundredFortyNineEQ_8209
      · exact prime_oneHundredFortyNineEQ_2790147475023173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2174787231250870885175220721) ^ 1087393615625435442587610360 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2174787231250870885175220721) ^ 724929077083623628391740240 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2174787231250870885175220721) ^ 434957446250174177035044144 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2174787231250870885175220721) ^ 167291325480836221936555440 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2174787231250870885175220721) ^ 928999244447189613487920 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2174787231250870885175220721) ^ 264927181295026298596080 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (7 : ZMod 2174787231250870885175220721) ^ 779452430640 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_2287763191315851190898608811 : Nat.Prime 2287763191315851190898608811 := by
  apply lucas_primality 2287763191315851190898608811 (2 : ZMod 2287763191315851190898608811)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (285068659, 1), (802530590118590059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (285068659, 1), (802530590118590059, 1)] : List FactorBlock).map factorBlockValue).prod) = 2287763191315851190898608811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_285068659
      · exact prime_oneHundredFortyNineEQ_802530590118590059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2287763191315851190898608811) ^ 1143881595657925595449304405 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2287763191315851190898608811) ^ 457552638263170238179721762 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2287763191315851190898608811) ^ 8025305901185900590 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2287763191315851190898608811) ^ 2850686590 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_3669953452735844618733184967 : Nat.Prime 3669953452735844618733184967 := by
  apply lucas_primality 3669953452735844618733184967 (5 : ZMod 3669953452735844618733184967)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1834976726367922309366592483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1834976726367922309366592483, 1)] : List FactorBlock).map factorBlockValue).prod) = 3669953452735844618733184967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_1834976726367922309366592483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 3669953452735844618733184967) ^ 1834976726367922309366592483 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3669953452735844618733184967) ^ 2 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_4761020695441095721599807527 : Nat.Prime 4761020695441095721599807527 := by
  apply lucas_primality 4761020695441095721599807527 (5 : ZMod 4761020695441095721599807527)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347, 1), (3581, 1), (80669, 1), (93241, 1), (98837, 1), (2576933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347, 1), (3581, 1), (80669, 1), (93241, 1), (98837, 1), (2576933, 1)] : List FactorBlock).map factorBlockValue).prod) = 4761020695441095721599807527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_347
      · exact prime_oneHundredFortyNineEQ_3581
      · exact prime_oneHundredFortyNineEQ_80669
      · exact prime_oneHundredFortyNineEQ_93241
      · exact prime_oneHundredFortyNineEQ_98837
      · exact prime_oneHundredFortyNineEQ_2576933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4761020695441095721599807527) ^ 2380510347720547860799903763 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4761020695441095721599807527) ^ 13720520736141486229394258 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4761020695441095721599807527) ^ 1329522673957301234738846 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4761020695441095721599807527) ^ 59019210544832534450654 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4761020695441095721599807527) ^ 51061450386000747756886 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4761020695441095721599807527) ^ 48170429044194944419598 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 4761020695441095721599807527) ^ 1847553155414244655022 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_7339906905471689237466369937 : Nat.Prime 7339906905471689237466369937 := by
  apply lucas_primality 7339906905471689237466369937 (5 : ZMod 7339906905471689237466369937)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1363412131, 1), (112155909222526097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1363412131, 1), (112155909222526097, 1)] : List FactorBlock).map factorBlockValue).prod) = 7339906905471689237466369937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_1363412131
      · exact prime_oneHundredFortyNineEQ_112155909222526097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7339906905471689237466369937) ^ 3669953452735844618733184968 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 7339906905471689237466369937) ^ 2446635635157229745822123312 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 7339906905471689237466369937) ^ 5383483642681252656 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 7339906905471689237466369937) ^ 65443782288 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_8807888286566027084959643921 : Nat.Prime 8807888286566027084959643921 := by
  apply lucas_primality 8807888286566027084959643921 (6 : ZMod 8807888286566027084959643921)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (149, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (149, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 8807888286566027084959643921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_5
      · exact prime_oneHundredFortyNineEQ_149
      · exact prime_oneHundredFortyNineEQ_171401
      · exact prime_oneHundredFortyNineEQ_714027719
      · exact prime_oneHundredFortyNineEQ_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8807888286566027084959643921) ^ 4403944143283013542479821960 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 8807888286566027084959643921) ^ 1761577657313205416991928784 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 8807888286566027084959643921) ^ 59113344205141121375568080 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 8807888286566027084959643921) ^ 51387613179421514955920 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 8807888286566027084959643921) ^ 12335499102053805680 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (6 : ZMod 8807888286566027084959643921) ^ 1458829975566682480 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_11009860358207533856199554903 : Nat.Prime 11009860358207533856199554903 := by
  apply lucas_primality 11009860358207533856199554903 (5 : ZMod 11009860358207533856199554903)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (56713, 1), (97066460584059508897427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (56713, 1), (97066460584059508897427, 1)] : List FactorBlock).map factorBlockValue).prod) = 11009860358207533856199554903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_56713
      · exact prime_oneHundredFortyNineEQ_97066460584059508897427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11009860358207533856199554903) ^ 5504930179103766928099777451 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11009860358207533856199554903) ^ 194132921168119017794854 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11009860358207533856199554903) ^ 113426 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_14679813810943378474932739867 : Nat.Prime 14679813810943378474932739867 := by
  apply lucas_primality 14679813810943378474932739867 (2 : ZMod 14679813810943378474932739867)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (281, 1), (198479, 1), (234588548083103947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (281, 1), (198479, 1), (234588548083103947, 1)] : List FactorBlock).map factorBlockValue).prod) = 14679813810943378474932739867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_11
      · exact prime_oneHundredFortyNineEQ_17
      · exact prime_oneHundredFortyNineEQ_281
      · exact prime_oneHundredFortyNineEQ_198479
      · exact prime_oneHundredFortyNineEQ_234588548083103947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14679813810943378474932739867) ^ 7339906905471689237466369933 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14679813810943378474932739867) ^ 4893271270314459491644246622 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14679813810943378474932739867) ^ 1334528528267579861357521806 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14679813810943378474932739867) ^ 863518459467257557348984698 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14679813810943378474932739867) ^ 52241330288054727668799786 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14679813810943378474932739867) ^ 73961546616737178618054 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 14679813810943378474932739867) ^ 62576856078 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_19573085081257837966576986497 : Nat.Prime 19573085081257837966576986497 := by
  apply lucas_primality 19573085081257837966576986497 (3 : ZMod 19573085081257837966576986497)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (1363412131, 1), (112155909222526097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (1363412131, 1), (112155909222526097, 1)] : List FactorBlock).map factorBlockValue).prod) = 19573085081257837966576986497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_1363412131
      · exact prime_oneHundredFortyNineEQ_112155909222526097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19573085081257837966576986497) ^ 9786542540628918983288493248 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 19573085081257837966576986497) ^ 14355956380483340416 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (3 : ZMod 19573085081257837966576986497) ^ 174516752768 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_22019720716415067712399109807 : Nat.Prime 22019720716415067712399109807 := by
  apply lucas_primality 22019720716415067712399109807 (5 : ZMod 22019720716415067712399109807)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11009860358207533856199554903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11009860358207533856199554903, 1)] : List FactorBlock).map factorBlockValue).prod) = 22019720716415067712399109807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_11009860358207533856199554903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 22019720716415067712399109807) ^ 11009860358207533856199554903 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 22019720716415067712399109807) ^ 2 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_35231553146264108339838575689 : Nat.Prime 35231553146264108339838575689 := by
  apply lucas_primality 35231553146264108339838575689 (17 : ZMod 35231553146264108339838575689)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (4807519, 1), (123263993, 1), (353887535123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (4807519, 1), (123263993, 1), (353887535123, 1)] : List FactorBlock).map factorBlockValue).prod) = 35231553146264108339838575689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3
      · exact prime_oneHundredFortyNineEQ_7
      · exact prime_oneHundredFortyNineEQ_4807519
      · exact prime_oneHundredFortyNineEQ_123263993
      · exact prime_oneHundredFortyNineEQ_353887535123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 35231553146264108339838575689) ^ 17615776573132054169919287844 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 35231553146264108339838575689) ^ 11743851048754702779946191896 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 35231553146264108339838575689) ^ 5033079020894872619976939384 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 35231553146264108339838575689) ^ 7328427229567705991352 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 35231553146264108339838575689) ^ 285821936226454292616 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (17 : ZMod 35231553146264108339838575689) ^ 99555790045045656 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_176157765731320541699192878487 : Nat.Prime 176157765731320541699192878487 := by
  apply lucas_primality 176157765731320541699192878487 (5 : ZMod 176157765731320541699192878487)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (105681467, 1), (8091624855127131943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (105681467, 1), (8091624855127131943, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_103
      · exact prime_oneHundredFortyNineEQ_105681467
      · exact prime_oneHundredFortyNineEQ_8091624855127131943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 176157765731320541699192878487) ^ 88078882865660270849596439243 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 176157765731320541699192878487) ^ 1710269570206995550477600762 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 176157765731320541699192878487) ^ 1666874720156189180258 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (5 : ZMod 176157765731320541699192878487) ^ 21770382202 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyNineEQ_176157765731320541699192878493 : Nat.Prime 176157765731320541699192878493 := by
  apply lucas_primality 176157765731320541699192878493 (2 : ZMod 176157765731320541699192878493)
  · rw [← oneHundredFortyNineEQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3547, 1), (12415968827975792338539109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3547, 1), (12415968827975792338539109, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyNineEQ_2
      · exact prime_oneHundredFortyNineEQ_3547
      · exact prime_oneHundredFortyNineEQ_12415968827975792338539109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 176157765731320541699192878493) ^ 88078882865660270849596439246 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 176157765731320541699192878493) ^ 49663875311903169354156436 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide
    · change (2 : ZMod 176157765731320541699192878493) ^ 14188 ≠ 1
      rw [← oneHundredFortyNineEQFastPow_eq_pow]
      decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878400 : Nat.totient 176157765731320541699192878400 = 69989791087434773799954432000 := by
  rw [← show ((([(2, 6), (5, 2), (149, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_149, prime_oneHundredFortyNineEQ_171401, prime_oneHundredFortyNineEQ_714027719, prime_oneHundredFortyNineEQ_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878401 : Nat.totient 176157765731320541699192878401 = 117438510487547027799461918880 := by
  rw [← show ((([(3, 4), (2174787231250870885175220721, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_2174787231250870885175220721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878402 : Nat.totient 176157765731320541699192878402 = 88028757872749329419538216000 := by
  rw [← show ((([(2, 1), (1999, 1), (14519, 1), (890105701, 1), (3409421658421, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_1999, prime_oneHundredFortyNineEQ_14519, prime_oneHundredFortyNineEQ_890105701, prime_oneHundredFortyNineEQ_3409421658421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878403 : Nat.totient 176157765731320541699192878403 = 160143423044185400353247750400 := by
  rw [← show ((([(11, 1), (754750231, 1), (1269335647, 1), (16715885089, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_11, prime_oneHundredFortyNineEQ_754750231, prime_oneHundredFortyNineEQ_1269335647, prime_oneHundredFortyNineEQ_16715885089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878404 : Nat.totient 176157765731320541699192878404 = 58719255243773513899730959464 := by
  rw [← show ((([(2, 2), (3, 1), (14679813810943378474932739867, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_14679813810943378474932739867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878405 : Nat.totient 176157765731320541699192878405 = 119952334718880849115818241536 := by
  rw [← show ((([(5, 1), (7, 2), (157, 1), (1663, 1), (285647317, 1), (9640812979727, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_157, prime_oneHundredFortyNineEQ_1663, prime_oneHundredFortyNineEQ_285647317, prime_oneHundredFortyNineEQ_9640812979727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878406 : Nat.totient 176157765731320541699192878406 = 88078882865650091952718900048 := by
  rw [← show ((([(2, 1), (8660455786187, 1), (10170236421752969, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_8660455786187, prime_oneHundredFortyNineEQ_10170236421752969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878407 : Nat.totient 176157765731320541699192878407 = 117438510370932334464227616192 := by
  rw [← show ((([(3, 1), (1007064437, 1), (58307346666610086937, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_1007064437, prime_oneHundredFortyNineEQ_58307346666610086937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878408 : Nat.totient 176157765731320541699192878408 = 86764272673635490687662163728 := by
  rw [← show ((([(2, 3), (67, 1), (328652548006195040483568803, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_67, prime_oneHundredFortyNineEQ_328652548006195040483568803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878409 : Nat.totient 176157765731320541699192878409 = 165626414564516938658980823040 := by
  rw [← show ((([(17, 1), (1409, 1), (3229, 1), (1094237, 1), (2081433011286961, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_17, prime_oneHundredFortyNineEQ_1409, prime_oneHundredFortyNineEQ_3229, prime_oneHundredFortyNineEQ_1094237, prime_oneHundredFortyNineEQ_2081433011286961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878410 : Nat.totient 176157765731320541699192878410 = 46645049905432579282468550400 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (151, 1), (2423, 1), (5349693768399919635113, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_151, prime_oneHundredFortyNineEQ_2423, prime_oneHundredFortyNineEQ_5349693768399919635113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878411 : Nat.totient 176157765731320541699192878411 = 162516640582990030657952916480 := by
  rw [← show ((([(13, 1), (2213, 1), (9533, 1), (4214200031, 1), (152416606553, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_13, prime_oneHundredFortyNineEQ_2213, prime_oneHundredFortyNineEQ_9533, prime_oneHundredFortyNineEQ_4214200031, prime_oneHundredFortyNineEQ_152416606553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878412 : Nat.totient 176157765731320541699192878412 = 75470179049105685548603537808 := by
  rw [← show ((([(2, 2), (7, 1), (2903, 1), (2167188693116979254209843, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_2903, prime_oneHundredFortyNineEQ_2167188693116979254209843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878413 : Nat.totient 176157765731320541699192878413 = 112241263281246519099092582400 := by
  rw [← show ((([(3, 1), (23, 2), (1307, 1), (21323, 1), (7966759, 1), (499941619201, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_23, prime_oneHundredFortyNineEQ_1307, prime_oneHundredFortyNineEQ_21323, prime_oneHundredFortyNineEQ_7966759, prime_oneHundredFortyNineEQ_499941619201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878414 : Nat.totient 176157765731320541699192878414 = 75855893659115506739418326400 := by
  rw [← show ((([(2, 1), (11, 1), (19, 1), (49991, 1), (8430118652521116083153, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_11, prime_oneHundredFortyNineEQ_19, prime_oneHundredFortyNineEQ_49991, prime_oneHundredFortyNineEQ_8430118652521116083153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878415 : Nat.totient 176157765731320541699192878415 = 133804740417915980001401978880 := by
  rw [← show ((([(5, 1), (31, 1), (53, 1), (59513, 1), (24262313, 1), (14850811348649, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_31, prime_oneHundredFortyNineEQ_53, prime_oneHundredFortyNineEQ_59513, prime_oneHundredFortyNineEQ_24262313, prime_oneHundredFortyNineEQ_14850811348649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878416 : Nat.totient 176157765731320541699192878416 = 58719255243773513899730959456 := by
  rw [← show ((([(2, 4), (3, 1), (3669953452735844618733184967, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_3669953452735844618733184967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878417 : Nat.totient 176157765731320541699192878417 = 176157765731212461673609697136 := by
  rw [← show ((([(1629907296733, 1), (108078395675884549, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_1629907296733, prime_oneHundredFortyNineEQ_108078395675884549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878418 : Nat.totient 176157765731320541699192878418 = 88078833822791835992707284816 := by
  rw [← show ((([(2, 1), (1795957, 1), (49042868434856887358437, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_1795957, prime_oneHundredFortyNineEQ_49042868434856887358437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878419 : Nat.totient 176157765731320541699192878419 = 100661580417875073598008144000 := by
  rw [← show ((([(3, 2), (7, 1), (4531104717001, 1), (617102271134213, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_4531104717001, prime_oneHundredFortyNineEQ_617102271134213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878420 : Nat.totient 176157765731320541699192878420 = 70463106292528216679677151360 := by
  rw [← show ((([(2, 2), (5, 1), (8807888286566027084959643921, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_8807888286566027084959643921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878421 : Nat.totient 176157765731320541699192878421 = 175790004216223839106918988844 := by
  rw [← show ((([(479, 1), (367761515096702592273889099, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_479, prime_oneHundredFortyNineEQ_367761515096702592273889099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878422 : Nat.totient 176157765731320541699192878422 = 56694453338815806523878167712 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (1012400952478853687926395853, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_29, prime_oneHundredFortyNineEQ_1012400952478853687926395853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878423 : Nat.totient 176157765731320541699192878423 = 173927920588926879007877904816 := by
  rw [← show ((([(79, 2), (26537680307, 1), (1063615488200429, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_79, prime_oneHundredFortyNineEQ_26537680307, prime_oneHundredFortyNineEQ_1063615488200429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878424 : Nat.totient 176157765731320541699192878424 = 80583932087782194878881536000 := by
  rw [← show ((([(2, 3), (13, 1), (113, 1), (728639, 1), (1977251, 1), (10404370135283, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_13, prime_oneHundredFortyNineEQ_113, prime_oneHundredFortyNineEQ_728639, prime_oneHundredFortyNineEQ_1977251, prime_oneHundredFortyNineEQ_10404370135283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878425 : Nat.totient 176157765731320541699192878425 = 82324803050849109075494400000 := by
  rw [← show ((([(3, 1), (5, 2), (11, 2), (37, 1), (107, 1), (69216950461, 1), (70836516601, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_11, prime_oneHundredFortyNineEQ_37, prime_oneHundredFortyNineEQ_107, prime_oneHundredFortyNineEQ_69216950461, prime_oneHundredFortyNineEQ_70836516601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878426 : Nat.totient 176157765731320541699192878426 = 70687070936723063517402120192 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (193, 1), (150654247, 1), (25455764715292237, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_17, prime_oneHundredFortyNineEQ_193, prime_oneHundredFortyNineEQ_150654247, prime_oneHundredFortyNineEQ_25455764715292237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878427 : Nat.totient 176157765731320541699192878427 = 176143046938510658299746694920 := by
  rw [← show ((([(11971, 1), (51551443, 1), (285450321333127859, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_11971, prime_oneHundredFortyNineEQ_51551443, prime_oneHundredFortyNineEQ_285450321333127859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878428 : Nat.totient 176157765731320541699192878428 = 58719155803549980977898305280 := by
  rw [← show ((([(2, 2), (3, 3), (594421, 1), (89474069, 1), (30668088350909, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_594421, prime_oneHundredFortyNineEQ_89474069, prime_oneHundredFortyNineEQ_30668088350909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878429 : Nat.totient 176157765731320541699192878429 = 176048958356304309953959410912 := by
  rw [← show ((([(1619, 1), (207377129, 1), (524679489052132279, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_1619, prime_oneHundredFortyNineEQ_207377129, prime_oneHundredFortyNineEQ_524679489052132279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878430 : Nat.totient 176157765731320541699192878430 = 70463106240578063106843323520 := by
  rw [← show ((([(2, 1), (5, 1), (1356359923, 1), (12987538391852097041, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_1356359923, prime_oneHundredFortyNineEQ_12987538391852097041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878431 : Nat.totient 176157765731320541699192878431 = 116536573897876223808531765600 := by
  rw [← show ((([(3, 1), (131, 1), (21347, 1), (20997732217507193530861, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_131, prime_oneHundredFortyNineEQ_21347, prime_oneHundredFortyNineEQ_20997732217507193530861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878432 : Nat.totient 176157765731320541699192878432 = 88077329802290925897453172992 := by
  rw [← show ((([(2, 5), (56713, 1), (97066460584059508897427, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_56713, prime_oneHundredFortyNineEQ_97066460584059508897427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878433 : Nat.totient 176157765731320541699192878433 = 142402582635331541971150480896 := by
  rw [← show ((([(7, 1), (19, 1), (227, 1), (20249, 1), (33479, 1), (103319, 1), (83304419687, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_19, prime_oneHundredFortyNineEQ_227, prime_oneHundredFortyNineEQ_20249, prime_oneHundredFortyNineEQ_33479, prime_oneHundredFortyNineEQ_103319, prime_oneHundredFortyNineEQ_83304419687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878434 : Nat.totient 176157765731320541699192878434 = 58689851510517138889639891392 := by
  rw [← show ((([(2, 1), (3, 1), (1997, 1), (2306115110149, 1), (6375165986363, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_1997, prime_oneHundredFortyNineEQ_2306115110149, prime_oneHundredFortyNineEQ_6375165986363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878435 : Nat.totient 176157765731320541699192878435 = 133898923533783969120055910400 := by
  rw [← show ((([(5, 1), (41, 1), (71, 1), (83, 1), (7369, 1), (59779, 1), (6394723, 1), (51764563, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_41, prime_oneHundredFortyNineEQ_71, prime_oneHundredFortyNineEQ_83, prime_oneHundredFortyNineEQ_7369, prime_oneHundredFortyNineEQ_59779, prime_oneHundredFortyNineEQ_6394723, prime_oneHundredFortyNineEQ_51764563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878436 : Nat.totient 176157765731320541699192878436 = 74068477487180924231195712000 := by
  rw [← show ((([(2, 2), (11, 1), (23, 1), (43, 1), (101, 1), (569197669, 1), (70415511541759, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_11, prime_oneHundredFortyNineEQ_23, prime_oneHundredFortyNineEQ_43, prime_oneHundredFortyNineEQ_101, prime_oneHundredFortyNineEQ_569197669, prime_oneHundredFortyNineEQ_70415511541759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878437 : Nat.totient 176157765731320541699192878437 = 108293089473663323500131552000 := by
  rw [← show ((([(3, 2), (13, 1), (971, 1), (2302681, 1), (673384203298663211, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_13, prime_oneHundredFortyNineEQ_971, prime_oneHundredFortyNineEQ_2302681, prime_oneHundredFortyNineEQ_673384203298663211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878438 : Nat.totient 176157765731320541699192878438 = 85723224163292268516645045504 := by
  rw [← show ((([(2, 1), (47, 1), (179, 1), (1770773, 1), (1208447179, 1), (4892494489, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_47, prime_oneHundredFortyNineEQ_179, prime_oneHundredFortyNineEQ_1770773, prime_oneHundredFortyNineEQ_1208447179, prime_oneHundredFortyNineEQ_4892494489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878439 : Nat.totient 176157765731320541699192878439 = 175307015367288110911264684416 := by
  rw [← show ((([(239, 1), (1543, 1), (347148433, 1), (1376013697575679, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_239, prime_oneHundredFortyNineEQ_1543, prime_oneHundredFortyNineEQ_347148433, prime_oneHundredFortyNineEQ_1376013697575679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878440 : Nat.totient 176157765731320541699192878440 = 40264623465046224263148754944 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (7, 1), (4807519, 1), (123263993, 1), (353887535123, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_4807519, prime_oneHundredFortyNineEQ_123263993, prime_oneHundredFortyNineEQ_353887535123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878441 : Nat.totient 176157765731320541699192878441 = 176157691776636105705043763584 := by
  rw [← show ((([(2381969, 1), (73954684435994146732889, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2381969, prime_oneHundredFortyNineEQ_73954684435994146732889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878442 : Nat.totient 176157765731320541699192878442 = 87803633843641302449527898112 := by
  rw [← show ((([(2, 1), (353, 1), (3413, 1), (73107309965197450217089, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_353, prime_oneHundredFortyNineEQ_3413, prime_oneHundredFortyNineEQ_73107309965197450217089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878443 : Nat.totient 176157765731320541699192878443 = 110530327706448709722144768000 := by
  rw [← show ((([(3, 1), (17, 2), (3475601, 1), (33458569, 1), (1747211259841, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_17, prime_oneHundredFortyNineEQ_3475601, prime_oneHundredFortyNineEQ_33458569, prime_oneHundredFortyNineEQ_1747211259841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878444 : Nat.totient 176157765731320541699192878444 = 87976821587716284440732478704 := by
  rw [← show ((([(2, 2), (863, 1), (51030638971993204431979397, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_863, prime_oneHundredFortyNineEQ_51030638971993204431979397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878445 : Nat.totient 176157765731320541699192878445 = 140926212585056433359354302752 := by
  rw [← show ((([(5, 1), (35231553146264108339838575689, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_35231553146264108339838575689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878446 : Nat.totient 176157765731320541699192878446 = 56824745911413497428383498240 := by
  rw [← show ((([(2, 1), (3, 2), (31, 1), (169313, 1), (13572193, 1), (137381186456993, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_31, prime_oneHundredFortyNineEQ_169313, prime_oneHundredFortyNineEQ_13572193, prime_oneHundredFortyNineEQ_137381186456993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878447 : Nat.totient 176157765731320541699192878447 = 137265791478951071453916528600 := by
  rw [← show ((([(7, 1), (11, 1), (2287763191315851190898608811, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_11, prime_oneHundredFortyNineEQ_2287763191315851190898608811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878448 : Nat.totient 176157765731320541699192878448 = 88078882865660270849596439216 := by
  rw [← show ((([(2, 4), (11009860358207533856199554903, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_11009860358207533856199554903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878449 : Nat.totient 176157765731320541699192878449 = 113866486605025346778883522560 := by
  rw [← show ((([(3, 1), (59, 1), (73, 1), (1871929, 1), (7283100358640709761, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_59, prime_oneHundredFortyNineEQ_73, prime_oneHundredFortyNineEQ_1871929, prime_oneHundredFortyNineEQ_7283100358640709761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878450 : Nat.totient 176157765731320541699192878450 = 65042867346949123088932754880 := by
  rw [← show ((([(2, 1), (5, 2), (13, 1), (271011947278954679537219813, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_13, prime_oneHundredFortyNineEQ_271011947278954679537219813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878451 : Nat.totient 176157765731320541699192878451 = 169715610185725379287462692000 := by
  rw [← show ((([(29, 1), (491, 1), (7951, 1), (1555967601680743158659, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_29, prime_oneHundredFortyNineEQ_491, prime_oneHundredFortyNineEQ_7951, prime_oneHundredFortyNineEQ_1555967601680743158659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878452 : Nat.totient 176157765731320541699192878452 = 54092004615168252905314391040 := by
  rw [← show ((([(2, 2), (3, 1), (19, 1), (61, 1), (89, 1), (5399, 1), (26359294192761377879, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_19, prime_oneHundredFortyNineEQ_61, prime_oneHundredFortyNineEQ_89, prime_oneHundredFortyNineEQ_5399, prime_oneHundredFortyNineEQ_26359294192761377879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878453 : Nat.totient 176157765731320541699192878453 = 175077008401002472309593000960 := by
  rw [← show ((([(163, 1), (5034233, 1), (2844626527, 1), (75466745441, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_163, prime_oneHundredFortyNineEQ_5034233, prime_oneHundredFortyNineEQ_2844626527, prime_oneHundredFortyNineEQ_75466745441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878454 : Nat.totient 176157765731320541699192878454 = 75496185311241180871243380480 := by
  rw [← show ((([(2, 1), (7, 2), (34601010113, 1), (51950166075435371, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_34601010113, prime_oneHundredFortyNineEQ_51950166075435371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878455 : Nat.totient 176157765731320541699192878455 = 93274903293706416324176938656 := by
  rw [← show ((([(3, 3), (5, 1), (139, 1), (9387570782377859936008147, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_139, prime_oneHundredFortyNineEQ_9387570782377859936008147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878456 : Nat.totient 176157765731320541699192878456 = 88078882865660270849596439224 := by
  rw [← show ((([(2, 3), (22019720716415067712399109807, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_22019720716415067712399109807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878457 : Nat.totient 176157765731320541699192878457 = 175582180265401119488557435200 := by
  rw [← show ((([(349, 1), (2749, 1), (25307, 1), (7255393330834666051, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_349, prime_oneHundredFortyNineEQ_2749, prime_oneHundredFortyNineEQ_25307, prime_oneHundredFortyNineEQ_7255393330834666051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878458 : Nat.totient 176157765731320541699192878458 = 53381039151379764614697938880 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (526223, 1), (99356077, 1), (51049747255103, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_11, prime_oneHundredFortyNineEQ_526223, prime_oneHundredFortyNineEQ_99356077, prime_oneHundredFortyNineEQ_51049747255103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878459 : Nat.totient 176157765731320541699192878459 = 168145674016735982865821670400 := by
  rw [← show ((([(23, 1), (593, 1), (2441, 1), (5291167189977644766341, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_23, prime_oneHundredFortyNineEQ_593, prime_oneHundredFortyNineEQ_2441, prime_oneHundredFortyNineEQ_5291167189977644766341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878460 : Nat.totient 176157765731320541699192878460 = 65590479551682591808064716800 := by
  rw [← show ((([(2, 2), (5, 1), (17, 1), (181, 1), (197, 1), (2473, 1), (2627671, 1), (2236057518949, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_17, prime_oneHundredFortyNineEQ_181, prime_oneHundredFortyNineEQ_197, prime_oneHundredFortyNineEQ_2473, prime_oneHundredFortyNineEQ_2627671, prime_oneHundredFortyNineEQ_2236057518949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878461 : Nat.totient 176157765731320541699192878461 = 100661580382841198909907393024 := by
  rw [← show ((([(3, 1), (7, 1), (2871430073, 1), (2921354454597852817, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_2871430073, prime_oneHundredFortyNineEQ_2921354454597852817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878462 : Nat.totient 176157765731320541699192878462 = 85424668067269334223260467200 := by
  rw [← show ((([(2, 1), (37, 1), (347, 1), (3581, 1), (80669, 1), (93241, 1), (98837, 1), (2576933, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_37, prime_oneHundredFortyNineEQ_347, prime_oneHundredFortyNineEQ_3581, prime_oneHundredFortyNineEQ_80669, prime_oneHundredFortyNineEQ_93241, prime_oneHundredFortyNineEQ_98837, prime_oneHundredFortyNineEQ_2576933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878463 : Nat.totient 176157765731320541699192878463 = 162607168366419569414022945504 := by
  rw [← show ((([(13, 1), (170584329373, 1), (79436355108082487, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_13, prime_oneHundredFortyNineEQ_170584329373, prime_oneHundredFortyNineEQ_79436355108082487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878464 : Nat.totient 176157765731320541699192878464 = 58719255200705644234730680320 := by
  rw [← show ((([(2, 7), (3, 2), (1363412131, 1), (112155909222526097, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_1363412131, prime_oneHundredFortyNineEQ_112155909222526097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878465 : Nat.totient 176157765731320541699192878465 = 140924527288150332542174559360 := by
  rw [← show ((([(5, 1), (83621, 1), (421324226525204294852233, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_83621, prime_oneHundredFortyNineEQ_421324226525204294852233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878466 : Nat.totient 176157765731320541699192878466 = 87145825989969676148521844736 := by
  rw [← show ((([(2, 1), (109, 1), (1033, 1), (2153, 1), (5598449, 1), (64898285272837, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_109, prime_oneHundredFortyNineEQ_1033, prime_oneHundredFortyNineEQ_2153, prime_oneHundredFortyNineEQ_5598449, prime_oneHundredFortyNineEQ_64898285272837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878467 : Nat.totient 176157765731320541699192878467 = 117221433758364870631625574240 := by
  rw [← show ((([(3, 1), (541, 1), (108538364591078583918171829, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_541, prime_oneHundredFortyNineEQ_108538364591078583918171829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878468 : Nat.totient 176157765731320541699192878468 = 74071728984984618420850786560 := by
  rw [← show ((([(2, 2), (7, 1), (53, 1), (41846434547, 1), (2836674024299641, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_53, prime_oneHundredFortyNineEQ_41846434547, prime_oneHundredFortyNineEQ_2836674024299641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878469 : Nat.totient 176157765731320541699192878469 = 160142756691762826205065537840 := by
  rw [← show ((([(11, 1), (240203, 1), (66670034675715783467693, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_11, prime_oneHundredFortyNineEQ_240203, prime_oneHundredFortyNineEQ_66670034675715783467693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878470 : Nat.totient 176157765731320541699192878470 = 46931598521395205344596080640 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (1321, 1), (5693, 1), (780794125616814757033, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_1321, prime_oneHundredFortyNineEQ_5693, prime_oneHundredFortyNineEQ_780794125616814757033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878471 : Nat.totient 176157765731320541699192878471 = 166886298876181666788189970488 := by
  rw [← show ((([(19, 1), (30338227, 1), (305603269244442943567, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_19, prime_oneHundredFortyNineEQ_30338227, prime_oneHundredFortyNineEQ_305603269244442943567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878472 : Nat.totient 176157765731320541699192878472 = 88031780427453233404552200000 := by
  rw [← show ((([(2, 3), (1871, 1), (3938251, 1), (20703919, 1), (144338459891, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_1871, prime_oneHundredFortyNineEQ_3938251, prime_oneHundredFortyNineEQ_20703919, prime_oneHundredFortyNineEQ_144338459891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878473 : Nat.totient 176157765731320541699192878473 = 117438510487547027799461918976 := by
  rw [← show ((([(3, 2), (19573085081257837966576986497, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_19573085081257837966576986497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878474 : Nat.totient 176157765731320541699192878474 = 86819139330634569359366553600 := by
  rw [← show ((([(2, 1), (97, 1), (277, 1), (2803, 1), (14401, 1), (55223977, 1), (1470540083, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_97, prime_oneHundredFortyNineEQ_277, prime_oneHundredFortyNineEQ_2803, prime_oneHundredFortyNineEQ_14401, prime_oneHundredFortyNineEQ_55223977, prime_oneHundredFortyNineEQ_1470540083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878475 : Nat.totient 176157765731320541699192878475 = 118991002523842958657365245600 := by
  rw [← show ((([(5, 2), (7, 1), (67, 1), (15024116480283201850677431, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_67, prime_oneHundredFortyNineEQ_15024116480283201850677431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878476 : Nat.totient 176157765731320541699192878476 = 52880379956869205763359961600 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (41, 1), (27541864560869378001749981, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_13, prime_oneHundredFortyNineEQ_41, prime_oneHundredFortyNineEQ_27541864560869378001749981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878477 : Nat.totient 176157765731320541699192878477 = 160447299463456629359630065920 := by
  rw [← show ((([(17, 1), (31, 1), (115231159, 1), (2900823119520630389, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_17, prime_oneHundredFortyNineEQ_31, prime_oneHundredFortyNineEQ_115231159, prime_oneHundredFortyNineEQ_2900823119520630389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878478 : Nat.totient 176157765731320541699192878478 = 88078831080475756944337399800 := by
  rw [← show ((([(2, 1), (1700851, 1), (51785184513905257338589, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_1700851, prime_oneHundredFortyNineEQ_51785184513905257338589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878479 : Nat.totient 176157765731320541699192878479 = 114707382336673841106451176600 := by
  rw [← show ((([(3, 1), (43, 1), (1365564075436593346505371151, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_43, prime_oneHundredFortyNineEQ_1365564075436593346505371151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878480 : Nat.totient 176157765731320541699192878480 = 61848400326068224691688499200 := by
  rw [← show ((([(2, 4), (5, 1), (11, 1), (29, 1), (656389, 1), (10516224017924241791, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_11, prime_oneHundredFortyNineEQ_29, prime_oneHundredFortyNineEQ_656389, prime_oneHundredFortyNineEQ_10516224017924241791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878481 : Nat.totient 176157765731320541699192878481 = 176157765729595933730756720112 := by
  rw [← show ((([(102143663597, 1), (1724607866292494773, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_102143663597, prime_oneHundredFortyNineEQ_1724607866292494773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878482 : Nat.totient 176157765731320541699192878482 = 47914331499143440148965039200 := by
  rw [← show ((([(2, 1), (3, 4), (7, 1), (23, 1), (211, 1), (32009467358200684189091, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_23, prime_oneHundredFortyNineEQ_211, prime_oneHundredFortyNineEQ_32009467358200684189091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878483 : Nat.totient 176157765731320541699192878483 = 174837646274607008939139605760 := by
  rw [← show ((([(137, 2), (5099, 1), (173382653, 1), (10616222279581, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_137, prime_oneHundredFortyNineEQ_5099, prime_oneHundredFortyNineEQ_173382653, prime_oneHundredFortyNineEQ_10616222279581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878484 : Nat.totient 176157765731320541699192878484 = 87840385287530706158569112160 := by
  rw [← show ((([(2, 2), (383, 1), (10303, 1), (1302012319, 1), (8571646159291, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_383, prime_oneHundredFortyNineEQ_10303, prime_oneHundredFortyNineEQ_1302012319, prime_oneHundredFortyNineEQ_8571646159291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878485 : Nat.totient 176157765731320541699192878485 = 91942138032292973428460612928 := by
  rw [← show ((([(3, 1), (5, 1), (47, 1), (9463, 1), (26404857999587874791059, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_47, prime_oneHundredFortyNineEQ_9463, prime_oneHundredFortyNineEQ_26404857999587874791059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878486 : Nat.totient 176157765731320541699192878486 = 87223747255211037840610671144 := by
  rw [← show ((([(2, 1), (103, 1), (105681467, 1), (8091624855127131943, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_103, prime_oneHundredFortyNineEQ_105681467, prime_oneHundredFortyNineEQ_8091624855127131943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878487 : Nat.totient 176157765731320541699192878487 = 176157765731320541699192878486 := by
  rw [← show ((([(176157765731320541699192878487, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_176157765731320541699192878487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878488 : Nat.totient 176157765731320541699192878488 = 58719255243773513899730959488 := by
  rw [← show ((([(2, 3), (3, 1), (7339906905471689237466369937, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_7339906905471689237466369937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878489 : Nat.totient 176157765731320541699192878489 = 139374929204050883867664042240 := by
  rw [← show ((([(7, 1), (13, 2), (52721, 1), (2824446868232487789623, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_13, prime_oneHundredFortyNineEQ_52721, prime_oneHundredFortyNineEQ_2824446868232487789623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878490 : Nat.totient 176157765731320541699192878490 = 66754521750816205275483617040 := by
  rw [← show ((([(2, 1), (5, 1), (19, 1), (927146135428002851048383571, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_19, prime_oneHundredFortyNineEQ_927146135428002851048383571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878491 : Nat.totient 176157765731320541699192878491 = 106762279939680207572805250800 := by
  rw [← show ((([(3, 2), (11, 1), (45984011, 1), (38695436355550624219, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_11, prime_oneHundredFortyNineEQ_45984011, prime_oneHundredFortyNineEQ_38695436355550624219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878492 : Nat.totient 176157765731320541699192878492 = 88054050928004319264919353936 := by
  rw [← show ((([(2, 2), (3547, 1), (12415968827975792338539109, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3547, prime_oneHundredFortyNineEQ_12415968827975792338539109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878493 : Nat.totient 176157765731320541699192878493 = 176157765731320541699192878492 := by
  rw [← show ((([(176157765731320541699192878493, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_176157765731320541699192878493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878494 : Nat.totient 176157765731320541699192878494 = 55055047636300284112653130112 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (263, 1), (6566680300131236177558819, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_17, prime_oneHundredFortyNineEQ_263, prime_oneHundredFortyNineEQ_6566680300131236177558819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878495 : Nat.totient 176157765731320541699192878495 = 140923510934219919806963331456 := by
  rw [← show ((([(5, 1), (52163, 1), (675412709128388097690673, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_52163, prime_oneHundredFortyNineEQ_675412709128388097690673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878496 : Nat.totient 176157765731320541699192878496 = 74833189619632318911190597632 := by
  rw [← show ((([(2, 5), (7, 1), (127, 1), (1777, 1), (2837, 1), (1228296715311627473, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_7, prime_oneHundredFortyNineEQ_127, prime_oneHundredFortyNineEQ_1777, prime_oneHundredFortyNineEQ_2837, prime_oneHundredFortyNineEQ_1228296715311627473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878497 : Nat.totient 176157765731320541699192878497 = 117436155413389986986875415808 := by
  rw [← show ((([(3, 1), (52067, 1), (1263259, 1), (17841617, 1), (50037012299, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_52067, prime_oneHundredFortyNineEQ_1263259, prime_oneHundredFortyNineEQ_17841617, prime_oneHundredFortyNineEQ_50037012299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878498 : Nat.totient 176157765731320541699192878498 = 87630229926471493567360454400 := by
  rw [← show ((([(2, 1), (367, 1), (421, 1), (7624021, 1), (92614853, 1), (807344539, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_367, prime_oneHundredFortyNineEQ_421, prime_oneHundredFortyNineEQ_7624021, prime_oneHundredFortyNineEQ_92614853, prime_oneHundredFortyNineEQ_807344539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878499 : Nat.totient 176157765731320541699192878499 = 171396745035879445977593070936 := by
  rw [← show ((([(37, 1), (4761020695441095721599807527, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_37, prime_oneHundredFortyNineEQ_4761020695441095721599807527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878500 : Nat.totient 176157765731320541699192878500 = 46975404194990443177874472000 := by
  rw [← show ((([(2, 2), (3, 2), (5, 3), (1791732796583, 1), (21848218795331, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_2, prime_oneHundredFortyNineEQ_3, prime_oneHundredFortyNineEQ_5, prime_oneHundredFortyNineEQ_1791732796583, prime_oneHundredFortyNineEQ_21848218795331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyNineEQ_176157765731320541699192878501 : Nat.totient 176157765731320541699192878501 = 176047735896385300886139040000 := by
  rw [← show ((([(1601, 1), (110029834935240813053836901, 1)] : List FactorBlock).map factorBlockValue).prod) = 176157765731320541699192878501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyNineEQ_1601, prime_oneHundredFortyNineEQ_110029834935240813053836901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFortyNineEQ : certifiedKill 1 176157765731320541699192878399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFortyNineEQ_176157765731320541699192878400, phi_oneHundredFortyNineEQ_176157765731320541699192878401, phi_oneHundredFortyNineEQ_176157765731320541699192878402,
    phi_oneHundredFortyNineEQ_176157765731320541699192878403, phi_oneHundredFortyNineEQ_176157765731320541699192878404, phi_oneHundredFortyNineEQ_176157765731320541699192878405,
    phi_oneHundredFortyNineEQ_176157765731320541699192878406, phi_oneHundredFortyNineEQ_176157765731320541699192878407, phi_oneHundredFortyNineEQ_176157765731320541699192878408,
    phi_oneHundredFortyNineEQ_176157765731320541699192878409, phi_oneHundredFortyNineEQ_176157765731320541699192878410, phi_oneHundredFortyNineEQ_176157765731320541699192878411,
    phi_oneHundredFortyNineEQ_176157765731320541699192878412, phi_oneHundredFortyNineEQ_176157765731320541699192878413, phi_oneHundredFortyNineEQ_176157765731320541699192878414,
    phi_oneHundredFortyNineEQ_176157765731320541699192878415, phi_oneHundredFortyNineEQ_176157765731320541699192878416, phi_oneHundredFortyNineEQ_176157765731320541699192878417,
    phi_oneHundredFortyNineEQ_176157765731320541699192878418, phi_oneHundredFortyNineEQ_176157765731320541699192878419, phi_oneHundredFortyNineEQ_176157765731320541699192878420,
    phi_oneHundredFortyNineEQ_176157765731320541699192878421, phi_oneHundredFortyNineEQ_176157765731320541699192878422, phi_oneHundredFortyNineEQ_176157765731320541699192878423,
    phi_oneHundredFortyNineEQ_176157765731320541699192878424, phi_oneHundredFortyNineEQ_176157765731320541699192878425, phi_oneHundredFortyNineEQ_176157765731320541699192878426,
    phi_oneHundredFortyNineEQ_176157765731320541699192878427, phi_oneHundredFortyNineEQ_176157765731320541699192878428, phi_oneHundredFortyNineEQ_176157765731320541699192878429,
    phi_oneHundredFortyNineEQ_176157765731320541699192878430, phi_oneHundredFortyNineEQ_176157765731320541699192878431, phi_oneHundredFortyNineEQ_176157765731320541699192878432,
    phi_oneHundredFortyNineEQ_176157765731320541699192878433, phi_oneHundredFortyNineEQ_176157765731320541699192878434, phi_oneHundredFortyNineEQ_176157765731320541699192878435,
    phi_oneHundredFortyNineEQ_176157765731320541699192878436, phi_oneHundredFortyNineEQ_176157765731320541699192878437, phi_oneHundredFortyNineEQ_176157765731320541699192878438,
    phi_oneHundredFortyNineEQ_176157765731320541699192878439, phi_oneHundredFortyNineEQ_176157765731320541699192878440, phi_oneHundredFortyNineEQ_176157765731320541699192878441,
    phi_oneHundredFortyNineEQ_176157765731320541699192878442, phi_oneHundredFortyNineEQ_176157765731320541699192878443, phi_oneHundredFortyNineEQ_176157765731320541699192878444,
    phi_oneHundredFortyNineEQ_176157765731320541699192878445, phi_oneHundredFortyNineEQ_176157765731320541699192878446, phi_oneHundredFortyNineEQ_176157765731320541699192878447,
    phi_oneHundredFortyNineEQ_176157765731320541699192878448, phi_oneHundredFortyNineEQ_176157765731320541699192878449, phi_oneHundredFortyNineEQ_176157765731320541699192878450,
    phi_oneHundredFortyNineEQ_176157765731320541699192878451, phi_oneHundredFortyNineEQ_176157765731320541699192878452, phi_oneHundredFortyNineEQ_176157765731320541699192878453,
    phi_oneHundredFortyNineEQ_176157765731320541699192878454, phi_oneHundredFortyNineEQ_176157765731320541699192878455, phi_oneHundredFortyNineEQ_176157765731320541699192878456,
    phi_oneHundredFortyNineEQ_176157765731320541699192878457, phi_oneHundredFortyNineEQ_176157765731320541699192878458, phi_oneHundredFortyNineEQ_176157765731320541699192878459,
    phi_oneHundredFortyNineEQ_176157765731320541699192878460, phi_oneHundredFortyNineEQ_176157765731320541699192878461, phi_oneHundredFortyNineEQ_176157765731320541699192878462,
    phi_oneHundredFortyNineEQ_176157765731320541699192878463, phi_oneHundredFortyNineEQ_176157765731320541699192878464, phi_oneHundredFortyNineEQ_176157765731320541699192878465,
    phi_oneHundredFortyNineEQ_176157765731320541699192878466, phi_oneHundredFortyNineEQ_176157765731320541699192878467, phi_oneHundredFortyNineEQ_176157765731320541699192878468,
    phi_oneHundredFortyNineEQ_176157765731320541699192878469, phi_oneHundredFortyNineEQ_176157765731320541699192878470, phi_oneHundredFortyNineEQ_176157765731320541699192878471,
    phi_oneHundredFortyNineEQ_176157765731320541699192878472, phi_oneHundredFortyNineEQ_176157765731320541699192878473, phi_oneHundredFortyNineEQ_176157765731320541699192878474,
    phi_oneHundredFortyNineEQ_176157765731320541699192878475, phi_oneHundredFortyNineEQ_176157765731320541699192878476, phi_oneHundredFortyNineEQ_176157765731320541699192878477,
    phi_oneHundredFortyNineEQ_176157765731320541699192878478, phi_oneHundredFortyNineEQ_176157765731320541699192878479, phi_oneHundredFortyNineEQ_176157765731320541699192878480,
    phi_oneHundredFortyNineEQ_176157765731320541699192878481, phi_oneHundredFortyNineEQ_176157765731320541699192878482, phi_oneHundredFortyNineEQ_176157765731320541699192878483,
    phi_oneHundredFortyNineEQ_176157765731320541699192878484, phi_oneHundredFortyNineEQ_176157765731320541699192878485, phi_oneHundredFortyNineEQ_176157765731320541699192878486,
    phi_oneHundredFortyNineEQ_176157765731320541699192878487, phi_oneHundredFortyNineEQ_176157765731320541699192878488, phi_oneHundredFortyNineEQ_176157765731320541699192878489,
    phi_oneHundredFortyNineEQ_176157765731320541699192878490, phi_oneHundredFortyNineEQ_176157765731320541699192878491, phi_oneHundredFortyNineEQ_176157765731320541699192878492,
    phi_oneHundredFortyNineEQ_176157765731320541699192878493, phi_oneHundredFortyNineEQ_176157765731320541699192878494, phi_oneHundredFortyNineEQ_176157765731320541699192878495,
    phi_oneHundredFortyNineEQ_176157765731320541699192878496, phi_oneHundredFortyNineEQ_176157765731320541699192878497, phi_oneHundredFortyNineEQ_176157765731320541699192878498,
    phi_oneHundredFortyNineEQ_176157765731320541699192878499, phi_oneHundredFortyNineEQ_176157765731320541699192878500, phi_oneHundredFortyNineEQ_176157765731320541699192878501]

end TotientTailPeriodKiller
end Erdos249257
