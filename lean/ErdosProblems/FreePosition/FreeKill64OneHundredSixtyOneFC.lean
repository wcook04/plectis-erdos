import Erdos249257.DiagonalPincerCertificatesT64
/- Kernel-checked off-diagonal certificate at a freely chosen position. -/
namespace Erdos249257
namespace TotientTailPeriodKiller
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private def oneHundredSixtyOneFCFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixtyOneFCFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixtyOneFCFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixtyOneFCFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixtyOneFCFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixtyOneFCFastPow a n * oneHundredSixtyOneFCFastPow a n * a else oneHundredSixtyOneFCFastPow a n * oneHundredSixtyOneFCFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixtyOneFC_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredSixtyOneFC_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredSixtyOneFC_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredSixtyOneFC_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredSixtyOneFC_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredSixtyOneFC_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredSixtyOneFC_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredSixtyOneFC_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredSixtyOneFC_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredSixtyOneFC_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredSixtyOneFC_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredSixtyOneFC_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredSixtyOneFC_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredSixtyOneFC_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredSixtyOneFC_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredSixtyOneFC_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredSixtyOneFC_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredSixtyOneFC_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredSixtyOneFC_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredSixtyOneFC_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredSixtyOneFC_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredSixtyOneFC_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredSixtyOneFC_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredSixtyOneFC_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredSixtyOneFC_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredSixtyOneFC_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredSixtyOneFC_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredSixtyOneFC_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredSixtyOneFC_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredSixtyOneFC_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredSixtyOneFC_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredSixtyOneFC_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredSixtyOneFC_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredSixtyOneFC_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredSixtyOneFC_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredSixtyOneFC_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredSixtyOneFC_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredSixtyOneFC_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredSixtyOneFC_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredSixtyOneFC_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredSixtyOneFC_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredSixtyOneFC_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredSixtyOneFC_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredSixtyOneFC_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredSixtyOneFC_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredSixtyOneFC_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredSixtyOneFC_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredSixtyOneFC_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredSixtyOneFC_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredSixtyOneFC_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredSixtyOneFC_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredSixtyOneFC_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredSixtyOneFC_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredSixtyOneFC_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredSixtyOneFC_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredSixtyOneFC_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredSixtyOneFC_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredSixtyOneFC_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredSixtyOneFC_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredSixtyOneFC_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredSixtyOneFC_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredSixtyOneFC_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredSixtyOneFC_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredSixtyOneFC_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredSixtyOneFC_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredSixtyOneFC_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredSixtyOneFC_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredSixtyOneFC_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredSixtyOneFC_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredSixtyOneFC_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredSixtyOneFC_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredSixtyOneFC_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredSixtyOneFC_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredSixtyOneFC_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredSixtyOneFC_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredSixtyOneFC_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredSixtyOneFC_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredSixtyOneFC_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredSixtyOneFC_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredSixtyOneFC_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredSixtyOneFC_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredSixtyOneFC_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredSixtyOneFC_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredSixtyOneFC_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredSixtyOneFC_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredSixtyOneFC_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredSixtyOneFC_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredSixtyOneFC_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredSixtyOneFC_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredSixtyOneFC_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredSixtyOneFC_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredSixtyOneFC_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredSixtyOneFC_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredSixtyOneFC_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredSixtyOneFC_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredSixtyOneFC_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredSixtyOneFC_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredSixtyOneFC_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredSixtyOneFC_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredSixtyOneFC_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredSixtyOneFC_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredSixtyOneFC_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredSixtyOneFC_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredSixtyOneFC_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredSixtyOneFC_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredSixtyOneFC_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredSixtyOneFC_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredSixtyOneFC_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredSixtyOneFC_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredSixtyOneFC_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredSixtyOneFC_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1873 : Nat.Prime 1873 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1913 : Nat.Prime 1913 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2459 : Nat.Prime 2459 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2467 : Nat.Prime 2467 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2503 : Nat.Prime 2503 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2531 : Nat.Prime 2531 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2777 : Nat.Prime 2777 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2927 : Nat.Prime 2927 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3037 : Nat.Prime 3037 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3137 : Nat.Prime 3137 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3163 : Nat.Prime 3163 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3251 : Nat.Prime 3251 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3701 : Nat.Prime 3701 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3847 : Nat.Prime 3847 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4127 : Nat.Prime 4127 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4133 : Nat.Prime 4133 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4441 : Nat.Prime 4441 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4493 : Nat.Prime 4493 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4513 : Nat.Prime 4513 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4567 : Nat.Prime 4567 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4751 : Nat.Prime 4751 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5419 : Nat.Prime 5419 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5743 : Nat.Prime 5743 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5813 : Nat.Prime 5813 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5897 : Nat.Prime 5897 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6067 : Nat.Prime 6067 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6173 : Nat.Prime 6173 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6271 : Nat.Prime 6271 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6277 : Nat.Prime 6277 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6379 : Nat.Prime 6379 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6547 : Nat.Prime 6547 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6659 : Nat.Prime 6659 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6871 : Nat.Prime 6871 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6883 : Nat.Prime 6883 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6917 : Nat.Prime 6917 := by norm_num

private theorem prime_oneHundredSixtyOneFC_7331 : Nat.Prime 7331 := by norm_num

private theorem prime_oneHundredSixtyOneFC_7537 : Nat.Prime 7537 := by norm_num

private theorem prime_oneHundredSixtyOneFC_7639 : Nat.Prime 7639 := by norm_num

private theorem prime_oneHundredSixtyOneFC_7873 : Nat.Prime 7873 := by norm_num

private theorem prime_oneHundredSixtyOneFC_8269 : Nat.Prime 8269 := by norm_num

private theorem prime_oneHundredSixtyOneFC_8431 : Nat.Prime 8431 := by norm_num

private theorem prime_oneHundredSixtyOneFC_8539 : Nat.Prime 8539 := by norm_num

private theorem prime_oneHundredSixtyOneFC_9091 : Nat.Prime 9091 := by norm_num

private theorem prime_oneHundredSixtyOneFC_9319 : Nat.Prime 9319 := by norm_num

private theorem prime_oneHundredSixtyOneFC_9323 : Nat.Prime 9323 := by norm_num

private theorem prime_oneHundredSixtyOneFC_9403 : Nat.Prime 9403 := by norm_num

private theorem prime_oneHundredSixtyOneFC_9769 : Nat.Prime 9769 := by norm_num

private theorem prime_oneHundredSixtyOneFC_10141 : Nat.Prime 10141 := by norm_num

private theorem prime_oneHundredSixtyOneFC_10211 : Nat.Prime 10211 := by norm_num

private theorem prime_oneHundredSixtyOneFC_10979 : Nat.Prime 10979 := by norm_num

private theorem prime_oneHundredSixtyOneFC_11411 : Nat.Prime 11411 := by norm_num

private theorem prime_oneHundredSixtyOneFC_11443 : Nat.Prime 11443 := by norm_num

private theorem prime_oneHundredSixtyOneFC_11813 : Nat.Prime 11813 := by norm_num

private theorem prime_oneHundredSixtyOneFC_11953 : Nat.Prime 11953 := by norm_num

private theorem prime_oneHundredSixtyOneFC_11971 : Nat.Prime 11971 := by norm_num

private theorem prime_oneHundredSixtyOneFC_12391 : Nat.Prime 12391 := by norm_num

private theorem prime_oneHundredSixtyOneFC_12457 : Nat.Prime 12457 := by norm_num

private theorem prime_oneHundredSixtyOneFC_12799 : Nat.Prime 12799 := by norm_num

private theorem prime_oneHundredSixtyOneFC_13063 : Nat.Prime 13063 := by norm_num

private theorem prime_oneHundredSixtyOneFC_13709 : Nat.Prime 13709 := by norm_num

private theorem prime_oneHundredSixtyOneFC_14149 : Nat.Prime 14149 := by norm_num

private theorem prime_oneHundredSixtyOneFC_14387 : Nat.Prime 14387 := by norm_num

private theorem prime_oneHundredSixtyOneFC_15121 : Nat.Prime 15121 := by norm_num

private theorem prime_oneHundredSixtyOneFC_15149 : Nat.Prime 15149 := by norm_num

private theorem prime_oneHundredSixtyOneFC_15527 : Nat.Prime 15527 := by norm_num

private theorem prime_oneHundredSixtyOneFC_15643 : Nat.Prime 15643 := by norm_num

private theorem prime_oneHundredSixtyOneFC_15731 : Nat.Prime 15731 := by norm_num

private theorem prime_oneHundredSixtyOneFC_15737 : Nat.Prime 15737 := by norm_num

private theorem prime_oneHundredSixtyOneFC_16573 : Nat.Prime 16573 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17207 : Nat.Prime 17207 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17231 : Nat.Prime 17231 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17417 : Nat.Prime 17417 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17467 : Nat.Prime 17467 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17509 : Nat.Prime 17509 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17783 : Nat.Prime 17783 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17987 : Nat.Prime 17987 := by norm_num

private theorem prime_oneHundredSixtyOneFC_18061 : Nat.Prime 18061 := by norm_num

private theorem prime_oneHundredSixtyOneFC_18973 : Nat.Prime 18973 := by norm_num

private theorem prime_oneHundredSixtyOneFC_20393 : Nat.Prime 20393 := by norm_num

private theorem prime_oneHundredSixtyOneFC_20663 : Nat.Prime 20663 := by norm_num

private theorem prime_oneHundredSixtyOneFC_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredSixtyOneFC_21569 : Nat.Prime 21569 := by norm_num

private theorem prime_oneHundredSixtyOneFC_22433 : Nat.Prime 22433 := by norm_num

private theorem prime_oneHundredSixtyOneFC_22907 : Nat.Prime 22907 := by norm_num

private theorem prime_oneHundredSixtyOneFC_23971 : Nat.Prime 23971 := by norm_num

private theorem prime_oneHundredSixtyOneFC_24391 : Nat.Prime 24391 := by norm_num

private theorem prime_oneHundredSixtyOneFC_25873 : Nat.Prime 25873 := by norm_num

private theorem prime_oneHundredSixtyOneFC_26891 : Nat.Prime 26891 := by norm_num

private theorem prime_oneHundredSixtyOneFC_27917 : Nat.Prime 27917 := by norm_num

private theorem prime_oneHundredSixtyOneFC_28019 : Nat.Prime 28019 := by norm_num

private theorem prime_oneHundredSixtyOneFC_28493 : Nat.Prime 28493 := by norm_num

private theorem prime_oneHundredSixtyOneFC_28813 : Nat.Prime 28813 := by norm_num

private theorem prime_oneHundredSixtyOneFC_28837 : Nat.Prime 28837 := by norm_num

private theorem prime_oneHundredSixtyOneFC_30139 : Nat.Prime 30139 := by norm_num

private theorem prime_oneHundredSixtyOneFC_30859 : Nat.Prime 30859 := by norm_num

private theorem prime_oneHundredSixtyOneFC_31019 : Nat.Prime 31019 := by norm_num

private theorem prime_oneHundredSixtyOneFC_32507 : Nat.Prime 32507 := by norm_num

private theorem prime_oneHundredSixtyOneFC_32563 : Nat.Prime 32563 := by norm_num

private theorem prime_oneHundredSixtyOneFC_33317 : Nat.Prime 33317 := by norm_num

private theorem prime_oneHundredSixtyOneFC_34141 : Nat.Prime 34141 := by norm_num

private theorem prime_oneHundredSixtyOneFC_36277 : Nat.Prime 36277 := by norm_num

private theorem prime_oneHundredSixtyOneFC_40519 : Nat.Prime 40519 := by norm_num

private theorem prime_oneHundredSixtyOneFC_44111 : Nat.Prime 44111 := by norm_num

private theorem prime_oneHundredSixtyOneFC_44797 : Nat.Prime 44797 := by norm_num

private theorem prime_oneHundredSixtyOneFC_45007 : Nat.Prime 45007 := by norm_num

private theorem prime_oneHundredSixtyOneFC_45247 : Nat.Prime 45247 := by norm_num

private theorem prime_oneHundredSixtyOneFC_46301 : Nat.Prime 46301 := by norm_num

private theorem prime_oneHundredSixtyOneFC_46477 : Nat.Prime 46477 := by norm_num

private theorem prime_oneHundredSixtyOneFC_47533 : Nat.Prime 47533 := by norm_num

private theorem prime_oneHundredSixtyOneFC_48281 : Nat.Prime 48281 := by norm_num

private theorem prime_oneHundredSixtyOneFC_49171 : Nat.Prime 49171 := by norm_num

private theorem prime_oneHundredSixtyOneFC_52579 : Nat.Prime 52579 := by norm_num

private theorem prime_oneHundredSixtyOneFC_58543 : Nat.Prime 58543 := by norm_num

private theorem prime_oneHundredSixtyOneFC_60659 : Nat.Prime 60659 := by norm_num

private theorem prime_oneHundredSixtyOneFC_63029 : Nat.Prime 63029 := by norm_num

private theorem prime_oneHundredSixtyOneFC_65033 : Nat.Prime 65033 := by norm_num

private theorem prime_oneHundredSixtyOneFC_70381 : Nat.Prime 70381 := by norm_num

private theorem prime_oneHundredSixtyOneFC_72167 : Nat.Prime 72167 := by norm_num

private theorem prime_oneHundredSixtyOneFC_73363 : Nat.Prime 73363 := by norm_num

private theorem prime_oneHundredSixtyOneFC_74699 : Nat.Prime 74699 := by norm_num

private theorem prime_oneHundredSixtyOneFC_80221 : Nat.Prime 80221 := by norm_num

private theorem prime_oneHundredSixtyOneFC_81043 : Nat.Prime 81043 := by norm_num

private theorem prime_oneHundredSixtyOneFC_83423 : Nat.Prime 83423 := by norm_num

private theorem prime_oneHundredSixtyOneFC_87037 : Nat.Prime 87037 := by norm_num

private theorem prime_oneHundredSixtyOneFC_90203 : Nat.Prime 90203 := by norm_num

private theorem prime_oneHundredSixtyOneFC_94397 : Nat.Prime 94397 := by norm_num

private theorem prime_oneHundredSixtyOneFC_97381 : Nat.Prime 97381 := by norm_num

private theorem prime_oneHundredSixtyOneFC_99551 : Nat.Prime 99551 := by norm_num

private theorem prime_oneHundredSixtyOneFC_102983 : Nat.Prime 102983 := by norm_num

private theorem prime_oneHundredSixtyOneFC_106801 : Nat.Prime 106801 := by norm_num

private theorem prime_oneHundredSixtyOneFC_107101 : Nat.Prime 107101 := by norm_num

private theorem prime_oneHundredSixtyOneFC_113501 : Nat.Prime 113501 := by norm_num

private theorem prime_oneHundredSixtyOneFC_114769 : Nat.Prime 114769 := by norm_num

private theorem prime_oneHundredSixtyOneFC_117833 : Nat.Prime 117833 := by norm_num

private theorem prime_oneHundredSixtyOneFC_121267 : Nat.Prime 121267 := by norm_num

private theorem prime_oneHundredSixtyOneFC_122399 : Nat.Prime 122399 := by norm_num

private theorem prime_oneHundredSixtyOneFC_130469 : Nat.Prime 130469 := by norm_num

private theorem prime_oneHundredSixtyOneFC_139493 : Nat.Prime 139493 := by norm_num

private theorem prime_oneHundredSixtyOneFC_141277 : Nat.Prime 141277 := by norm_num

private theorem prime_oneHundredSixtyOneFC_145829 : Nat.Prime 145829 := by norm_num

private theorem prime_oneHundredSixtyOneFC_147107 : Nat.Prime 147107 := by norm_num

private theorem prime_oneHundredSixtyOneFC_149371 : Nat.Prime 149371 := by norm_num

private theorem prime_oneHundredSixtyOneFC_155539 : Nat.Prime 155539 := by norm_num

private theorem prime_oneHundredSixtyOneFC_157007 : Nat.Prime 157007 := by norm_num

private theorem prime_oneHundredSixtyOneFC_157627 : Nat.Prime 157627 := by norm_num

private theorem prime_oneHundredSixtyOneFC_162787 : Nat.Prime 162787 := by norm_num

private theorem prime_oneHundredSixtyOneFC_164071 : Nat.Prime 164071 := by norm_num

private theorem prime_oneHundredSixtyOneFC_164471 : Nat.Prime 164471 := by norm_num

private theorem prime_oneHundredSixtyOneFC_168043 : Nat.Prime 168043 := by norm_num

private theorem prime_oneHundredSixtyOneFC_168643 : Nat.Prime 168643 := by norm_num

private theorem prime_oneHundredSixtyOneFC_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredSixtyOneFC_174467 : Nat.Prime 174467 := by norm_num

private theorem prime_oneHundredSixtyOneFC_194581 : Nat.Prime 194581 := by norm_num

private theorem prime_oneHundredSixtyOneFC_195469 : Nat.Prime 195469 := by norm_num

private theorem prime_oneHundredSixtyOneFC_200909 : Nat.Prime 200909 := by norm_num

private theorem prime_oneHundredSixtyOneFC_209819 : Nat.Prime 209819 := by norm_num

private theorem prime_oneHundredSixtyOneFC_215863 : Nat.Prime 215863 := by norm_num

private theorem prime_oneHundredSixtyOneFC_222601 : Nat.Prime 222601 := by norm_num

private theorem prime_oneHundredSixtyOneFC_222659 : Nat.Prime 222659 := by norm_num

private theorem prime_oneHundredSixtyOneFC_225241 : Nat.Prime 225241 := by norm_num

private theorem prime_oneHundredSixtyOneFC_245981 : Nat.Prime 245981 := by norm_num

private theorem prime_oneHundredSixtyOneFC_260171 : Nat.Prime 260171 := by norm_num

private theorem prime_oneHundredSixtyOneFC_260921 : Nat.Prime 260921 := by norm_num

private theorem prime_oneHundredSixtyOneFC_270073 : Nat.Prime 270073 := by norm_num

private theorem prime_oneHundredSixtyOneFC_271163 : Nat.Prime 271163 := by norm_num

private theorem prime_oneHundredSixtyOneFC_289171 : Nat.Prime 289171 := by norm_num

private theorem prime_oneHundredSixtyOneFC_297191 : Nat.Prime 297191 := by norm_num

private theorem prime_oneHundredSixtyOneFC_306883 : Nat.Prime 306883 := by norm_num

private theorem prime_oneHundredSixtyOneFC_310567 : Nat.Prime 310567 := by norm_num

private theorem prime_oneHundredSixtyOneFC_317351 : Nat.Prime 317351 := by norm_num

private theorem prime_oneHundredSixtyOneFC_329711 : Nat.Prime 329711 := by norm_num

private theorem prime_oneHundredSixtyOneFC_365039 : Nat.Prime 365039 := by norm_num

private theorem prime_oneHundredSixtyOneFC_371387 : Nat.Prime 371387 := by norm_num

private theorem prime_oneHundredSixtyOneFC_403219 : Nat.Prime 403219 := by norm_num

private theorem prime_oneHundredSixtyOneFC_404951 : Nat.Prime 404951 := by norm_num

private theorem prime_oneHundredSixtyOneFC_416359 : Nat.Prime 416359 := by norm_num

private theorem prime_oneHundredSixtyOneFC_418373 : Nat.Prime 418373 := by norm_num

private theorem prime_oneHundredSixtyOneFC_432499 : Nat.Prime 432499 := by norm_num

private theorem prime_oneHundredSixtyOneFC_442121 : Nat.Prime 442121 := by norm_num

private theorem prime_oneHundredSixtyOneFC_463339 : Nat.Prime 463339 := by norm_num

private theorem prime_oneHundredSixtyOneFC_464917 : Nat.Prime 464917 := by norm_num

private theorem prime_oneHundredSixtyOneFC_478991 : Nat.Prime 478991 := by norm_num

private theorem prime_oneHundredSixtyOneFC_487727 : Nat.Prime 487727 := by norm_num

private theorem prime_oneHundredSixtyOneFC_497677 : Nat.Prime 497677 := by norm_num

private theorem prime_oneHundredSixtyOneFC_499739 : Nat.Prime 499739 := by norm_num

private theorem prime_oneHundredSixtyOneFC_512609 : Nat.Prime 512609 := by norm_num

private theorem prime_oneHundredSixtyOneFC_515369 : Nat.Prime 515369 := by norm_num

private theorem prime_oneHundredSixtyOneFC_564701 : Nat.Prime 564701 := by norm_num

private theorem prime_oneHundredSixtyOneFC_571783 : Nat.Prime 571783 := by norm_num

private theorem prime_oneHundredSixtyOneFC_581173 : Nat.Prime 581173 := by norm_num

private theorem prime_oneHundredSixtyOneFC_612169 : Nat.Prime 612169 := by norm_num

private theorem prime_oneHundredSixtyOneFC_617327 : Nat.Prime 617327 := by norm_num

private theorem prime_oneHundredSixtyOneFC_624787 : Nat.Prime 624787 := by norm_num

private theorem prime_oneHundredSixtyOneFC_660277 : Nat.Prime 660277 := by norm_num

private theorem prime_oneHundredSixtyOneFC_707099 : Nat.Prime 707099 := by norm_num

private theorem prime_oneHundredSixtyOneFC_707827 : Nat.Prime 707827 := by norm_num

private theorem prime_oneHundredSixtyOneFC_725317 : Nat.Prime 725317 := by norm_num

private theorem prime_oneHundredSixtyOneFC_740143 : Nat.Prime 740143 := by norm_num

private theorem prime_oneHundredSixtyOneFC_771643 : Nat.Prime 771643 := by norm_num

private theorem prime_oneHundredSixtyOneFC_833689 : Nat.Prime 833689 := by norm_num

private theorem prime_oneHundredSixtyOneFC_909343 : Nat.Prime 909343 := by norm_num

private theorem prime_oneHundredSixtyOneFC_920377 : Nat.Prime 920377 := by norm_num

private theorem prime_oneHundredSixtyOneFC_939791 : Nat.Prime 939791 := by norm_num

private theorem prime_oneHundredSixtyOneFC_955039 : Nat.Prime 955039 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1035607 : Nat.Prime 1035607 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1081051 : Nat.Prime 1081051 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1110539 : Nat.Prime 1110539 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1170581 : Nat.Prime 1170581 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1218953 : Nat.Prime 1218953 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1246181 : Nat.Prime 1246181 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1311481 : Nat.Prime 1311481 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1514033 : Nat.Prime 1514033 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1518589 : Nat.Prime 1518589 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1563329 : Nat.Prime 1563329 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1639307 : Nat.Prime 1639307 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1723669 : Nat.Prime 1723669 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1769099 : Nat.Prime 1769099 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1819381 : Nat.Prime 1819381 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1822307 : Nat.Prime 1822307 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1883881 : Nat.Prime 1883881 := by norm_num

private theorem prime_oneHundredSixtyOneFC_1948313 : Nat.Prime 1948313 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2156311 : Nat.Prime 2156311 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2271439 : Nat.Prime 2271439 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2326367 : Nat.Prime 2326367 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2344333 : Nat.Prime 2344333 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2460629 : Nat.Prime 2460629 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2489909 : Nat.Prime 2489909 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2802871 : Nat.Prime 2802871 := by norm_num

private theorem prime_oneHundredSixtyOneFC_2971607 : Nat.Prime 2971607 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3062107 : Nat.Prime 3062107 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3103423 : Nat.Prime 3103423 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3163067 : Nat.Prime 3163067 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3177271 : Nat.Prime 3177271 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3336451 : Nat.Prime 3336451 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3493333 : Nat.Prime 3493333 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3572897 : Nat.Prime 3572897 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3579119 : Nat.Prime 3579119 := by norm_num

private theorem prime_oneHundredSixtyOneFC_3818587 : Nat.Prime 3818587 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4184711 : Nat.Prime 4184711 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4201583 : Nat.Prime 4201583 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4203967 : Nat.Prime 4203967 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4282273 : Nat.Prime 4282273 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4291097 : Nat.Prime 4291097 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4347191 : Nat.Prime 4347191 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4498027 : Nat.Prime 4498027 := by norm_num

private theorem prime_oneHundredSixtyOneFC_4629127 : Nat.Prime 4629127 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5004149 : Nat.Prime 5004149 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5048917 : Nat.Prime 5048917 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5096737 : Nat.Prime 5096737 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5395279 : Nat.Prime 5395279 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5505883 : Nat.Prime 5505883 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5619701 : Nat.Prime 5619701 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5680691 : Nat.Prime 5680691 := by norm_num

private theorem prime_oneHundredSixtyOneFC_5806357 : Nat.Prime 5806357 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6122287 : Nat.Prime 6122287 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6170579 : Nat.Prime 6170579 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6272867 : Nat.Prime 6272867 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6314617 : Nat.Prime 6314617 := by norm_num

private theorem prime_oneHundredSixtyOneFC_6984071 : Nat.Prime 6984071 := by norm_num

private theorem prime_oneHundredSixtyOneFC_7591387 : Nat.Prime 7591387 := by norm_num

private theorem prime_oneHundredSixtyOneFC_7669967 : Nat.Prime 7669967 := by norm_num

private theorem prime_oneHundredSixtyOneFC_7754323 : Nat.Prime 7754323 := by norm_num

private theorem prime_oneHundredSixtyOneFC_8456419 : Nat.Prime 8456419 := by norm_num

private theorem prime_oneHundredSixtyOneFC_9387527 : Nat.Prime 9387527 := by norm_num

private theorem prime_oneHundredSixtyOneFC_9545399 : Nat.Prime 9545399 := by norm_num

private theorem prime_oneHundredSixtyOneFC_9642827 : Nat.Prime 9642827 := by norm_num

private theorem prime_oneHundredSixtyOneFC_9764267 : Nat.Prime 9764267 := by norm_num

private theorem prime_oneHundredSixtyOneFC_10090943 : Nat.Prime 10090943 := by norm_num

private theorem prime_oneHundredSixtyOneFC_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredSixtyOneFC_10936069 : Nat.Prime 10936069 := by norm_num

private theorem prime_oneHundredSixtyOneFC_11762479 : Nat.Prime 11762479 := by norm_num

private theorem prime_oneHundredSixtyOneFC_12201611 : Nat.Prime 12201611 := by norm_num

private theorem prime_oneHundredSixtyOneFC_12535219 : Nat.Prime 12535219 := by norm_num

private theorem prime_oneHundredSixtyOneFC_13416959 : Nat.Prime 13416959 := by norm_num

private theorem prime_oneHundredSixtyOneFC_13720877 : Nat.Prime 13720877 := by norm_num

private theorem prime_oneHundredSixtyOneFC_14336549 : Nat.Prime 14336549 := by norm_num

private theorem prime_oneHundredSixtyOneFC_15362491 : Nat.Prime 15362491 := by norm_num

private theorem prime_oneHundredSixtyOneFC_15964331 : Nat.Prime 15964331 := by norm_num

private theorem prime_oneHundredSixtyOneFC_16678771 : Nat.Prime 16678771 := by norm_num

private theorem prime_oneHundredSixtyOneFC_16799953 : Nat.Prime 16799953 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17436157 : Nat.Prime 17436157 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17649631 : Nat.Prime 17649631 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17741279 : Nat.Prime 17741279 := by norm_num

private theorem prime_oneHundredSixtyOneFC_17902243 : Nat.Prime 17902243 := by norm_num

private theorem prime_oneHundredSixtyOneFC_23956067 : Nat.Prime 23956067 := by norm_num

private theorem prime_oneHundredSixtyOneFC_25493933 : Nat.Prime 25493933 := by norm_num

private theorem prime_oneHundredSixtyOneFC_28553171 : Nat.Prime 28553171 := by norm_num

private theorem prime_oneHundredSixtyOneFC_30291409 : Nat.Prime 30291409 := by
  apply lucas_primality 30291409 (13 : ZMod 30291409)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 6), (7, 2), (53, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 6), (7, 2), (53, 1)] : List FactorBlock).map factorBlockValue).prod) = 30291409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_53
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 30291409) ^ 15145704 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 30291409) ^ 10097136 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 30291409) ^ 4327344 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 30291409) ^ 571536 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_30293503 : Nat.Prime 30293503 := by
  apply lucas_primality 30293503 (3 : ZMod 30293503)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5048917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5048917, 1)] : List FactorBlock).map factorBlockValue).prod) = 30293503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5048917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 30293503) ^ 15146751 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 30293503) ^ 10097834 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 30293503) ^ 6 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_31266581 : Nat.Prime 31266581 := by
  apply lucas_primality 31266581 (3 : ZMod 31266581)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1563329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1563329, 1)] : List FactorBlock).map factorBlockValue).prod) = 31266581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_1563329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31266581) ^ 15633290 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 31266581) ^ 6253316 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 31266581) ^ 20 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_32158261 : Nat.Prime 32158261 := by
  apply lucas_primality 32158261 (2 : ZMod 32158261)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (19, 1), (9403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (19, 1), (9403, 1)] : List FactorBlock).map factorBlockValue).prod) = 32158261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_9403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32158261) ^ 16079130 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32158261) ^ 10719420 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32158261) ^ 6431652 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32158261) ^ 1692540 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32158261) ^ 3420 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_32334163 : Nat.Prime 32334163 := by
  apply lucas_primality 32334163 (2 : ZMod 32334163)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (40519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (40519, 1)] : List FactorBlock).map factorBlockValue).prod) = 32334163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_40519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32334163) ^ 16167081 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32334163) ^ 10778054 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32334163) ^ 4619166 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32334163) ^ 1701798 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32334163) ^ 798 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_32701811 : Nat.Prime 32701811 := by
  apply lucas_primality 32701811 (2 : ZMod 32701811)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) = 32701811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_73
      · exact prime_oneHundredSixtyOneFC_44797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32701811) ^ 16350905 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 6540362 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 447970 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 730 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_33444289 : Nat.Prime 33444289 := by
  apply lucas_primality 33444289 (11 : ZMod 33444289)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (31, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (31, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) = 33444289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_1873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 33444289) ^ 16722144 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 33444289) ^ 11148096 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 33444289) ^ 1078848 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 33444289) ^ 17856 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_34858727 : Nat.Prime 34858727 := by
  apply lucas_primality 34858727 (7 : ZMod 34858727)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) = 34858727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_2489909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34858727) ^ 17429363 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 4979818 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 14 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_34897321 : Nat.Prime 34897321 := by
  apply lucas_primality 34897321 (19 : ZMod 34897321)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (31, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (31, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) = 34897321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_53
      · exact prime_oneHundredSixtyOneFC_59
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 34897321) ^ 17448660 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 34897321) ^ 11632440 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 34897321) ^ 6979464 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 34897321) ^ 1125720 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 34897321) ^ 658440 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 34897321) ^ 591480 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_36763897 : Nat.Prime 36763897 := by
  apply lucas_primality 36763897 (15 : ZMod 36763897)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (117833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (117833, 1)] : List FactorBlock).map factorBlockValue).prod) = 36763897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_117833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 36763897) ^ 18381948 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (15 : ZMod 36763897) ^ 12254632 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (15 : ZMod 36763897) ^ 2827992 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (15 : ZMod 36763897) ^ 312 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_40674451 : Nat.Prime 40674451 := by
  apply lucas_primality 40674451 (2 : ZMod 40674451)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) = 40674451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_271163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40674451) ^ 20337225 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 13558150 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 8134890 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 150 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_44976511 : Nat.Prime 44976511 := by
  apply lucas_primality 44976511 (41 : ZMod 44976511)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (499739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (499739, 1)] : List FactorBlock).map factorBlockValue).prod) = 44976511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_499739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (41 : ZMod 44976511) ^ 22488255 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (41 : ZMod 44976511) ^ 14992170 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (41 : ZMod 44976511) ^ 8995302 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (41 : ZMod 44976511) ^ 90 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_48125003 : Nat.Prime 48125003 := by
  apply lucas_primality 48125003 (2 : ZMod 48125003)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (313, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (313, 1), (1303, 1)] : List FactorBlock).map factorBlockValue).prod) = 48125003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_59
      · exact prime_oneHundredSixtyOneFC_313
      · exact prime_oneHundredSixtyOneFC_1303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48125003) ^ 24062501 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 48125003) ^ 815678 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 48125003) ^ 153754 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 48125003) ^ 36934 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_52413019 : Nat.Prime 52413019 := by
  apply lucas_primality 52413019 (3 : ZMod 52413019)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (199, 1), (6271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (199, 1), (6271, 1)] : List FactorBlock).map factorBlockValue).prod) = 52413019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_199
      · exact prime_oneHundredSixtyOneFC_6271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52413019) ^ 26206509 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 52413019) ^ 17471006 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 52413019) ^ 7487574 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 52413019) ^ 263382 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 52413019) ^ 8358 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_54845737 : Nat.Prime 54845737 := by
  apply lucas_primality 54845737 (5 : ZMod 54845737)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (83, 1), (2503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (83, 1), (2503, 1)] : List FactorBlock).map factorBlockValue).prod) = 54845737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_83
      · exact prime_oneHundredSixtyOneFC_2503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54845737) ^ 27422868 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 54845737) ^ 18281912 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 54845737) ^ 4985976 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 54845737) ^ 660792 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 54845737) ^ 21912 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_55925861 : Nat.Prime 55925861 := by
  apply lucas_primality 55925861 (2 : ZMod 55925861)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (90203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (90203, 1)] : List FactorBlock).map factorBlockValue).prod) = 55925861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_90203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55925861) ^ 27962930 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 55925861) ^ 11185172 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 55925861) ^ 1804060 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 55925861) ^ 620 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_58233839 : Nat.Prime 58233839 := by
  apply lucas_primality 58233839 (11 : ZMod 58233839)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (97381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (97381, 1)] : List FactorBlock).map factorBlockValue).prod) = 58233839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_23
      · exact prime_oneHundredSixtyOneFC_97381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 58233839) ^ 29116919 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 58233839) ^ 4479526 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 58233839) ^ 2531906 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 58233839) ^ 598 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_62319643 : Nat.Prime 62319643 := by
  apply lucas_primality 62319643 (3 : ZMod 62319643)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (43, 1), (3137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (43, 1), (3137, 1)] : List FactorBlock).map factorBlockValue).prod) = 62319643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_43
      · exact prime_oneHundredSixtyOneFC_3137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 62319643) ^ 31159821 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 62319643) ^ 20773214 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 62319643) ^ 8902806 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 62319643) ^ 5665422 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 62319643) ^ 1449294 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 62319643) ^ 19866 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_69292543 : Nat.Prime 69292543 := by
  apply lucas_primality 69292543 (3 : ZMod 69292543)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (29, 1), (41, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (29, 1), (41, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 69292543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_29
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69292543) ^ 34646271 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 69292543) ^ 23097514 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 69292543) ^ 6299322 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 69292543) ^ 2389398 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 69292543) ^ 1690062 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 69292543) ^ 78474 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_70830061 : Nat.Prime 70830061 := by
  apply lucas_primality 70830061 (6 : ZMod 70830061)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (168643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (168643, 1)] : List FactorBlock).map factorBlockValue).prod) = 70830061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_168643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 70830061) ^ 35415030 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 70830061) ^ 23610020 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 70830061) ^ 14166012 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 70830061) ^ 10118580 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 70830061) ^ 420 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_71375501 : Nat.Prime 71375501 := by
  apply lucas_primality 71375501 (2 : ZMod 71375501)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (7, 1), (20393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (7, 1), (20393, 1)] : List FactorBlock).map factorBlockValue).prod) = 71375501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_20393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 71375501) ^ 35687750 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 71375501) ^ 14275100 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 71375501) ^ 10196500 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 71375501) ^ 3500 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_71608973 : Nat.Prime 71608973 := by
  apply lucas_primality 71608973 (2 : ZMod 71608973)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17902243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17902243, 1)] : List FactorBlock).map factorBlockValue).prod) = 71608973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_17902243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 71608973) ^ 35804486 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 71608973) ^ 4 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_71968433 : Nat.Prime 71968433 := by
  apply lucas_primality 71968433 (3 : ZMod 71968433)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4498027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4498027, 1)] : List FactorBlock).map factorBlockValue).prod) = 71968433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_4498027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 71968433) ^ 35984216 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 71968433) ^ 16 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_80445121 : Nat.Prime 80445121 := by
  apply lucas_primality 80445121 (37 : ZMod 80445121)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (7, 1), (11971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (7, 1), (11971, 1)] : List FactorBlock).map factorBlockValue).prod) = 80445121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_11971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 80445121) ^ 40222560 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (37 : ZMod 80445121) ^ 26815040 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (37 : ZMod 80445121) ^ 16089024 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (37 : ZMod 80445121) ^ 11492160 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (37 : ZMod 80445121) ^ 6720 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_83822311 : Nat.Prime 83822311 := by
  apply lucas_primality 83822311 (6 : ZMod 83822311)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (11, 1), (13, 2), (167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (11, 1), (13, 2), (167, 1)] : List FactorBlock).map factorBlockValue).prod) = 83822311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 83822311) ^ 41911155 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 83822311) ^ 27940770 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 83822311) ^ 16764462 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 83822311) ^ 7620210 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 83822311) ^ 6447870 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 83822311) ^ 501930 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_102211363 : Nat.Prime 102211363 := by
  apply lucas_primality 102211363 (3 : ZMod 102211363)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 2), (15643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 2), (15643, 1)] : List FactorBlock).map factorBlockValue).prod) = 102211363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_15643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 102211363) ^ 51105681 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 102211363) ^ 34070454 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 102211363) ^ 9291942 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 102211363) ^ 6534 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_111896423 : Nat.Prime 111896423 := by
  apply lucas_primality 111896423 (5 : ZMod 111896423)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (31, 1), (164071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (31, 1), (164071, 1)] : List FactorBlock).map factorBlockValue).prod) = 111896423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_164071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 111896423) ^ 55948211 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 111896423) ^ 10172402 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 111896423) ^ 3609562 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 111896423) ^ 682 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_117394327 : Nat.Prime 117394327 := by
  apply lucas_primality 117394327 (5 : ZMod 117394327)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (310567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (310567, 1)] : List FactorBlock).map factorBlockValue).prod) = 117394327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_310567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 117394327) ^ 58697163 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 117394327) ^ 39131442 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 117394327) ^ 16770618 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 117394327) ^ 378 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_121710551 : Nat.Prime 121710551 := by
  apply lucas_primality 121710551 (7 : ZMod 121710551)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (41, 1), (4567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (41, 1), (4567, 1)] : List FactorBlock).map factorBlockValue).prod) = 121710551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_4567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 121710551) ^ 60855275 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 121710551) ^ 24342110 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 121710551) ^ 9362350 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 121710551) ^ 2968550 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 121710551) ^ 26650 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_124233581 : Nat.Prime 124233581 := by
  apply lucas_primality 124233581 (2 : ZMod 124233581)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (270073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (270073, 1)] : List FactorBlock).map factorBlockValue).prod) = 124233581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_23
      · exact prime_oneHundredSixtyOneFC_270073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 124233581) ^ 62116790 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 124233581) ^ 24846716 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 124233581) ^ 5401460 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 124233581) ^ 460 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_134499857 : Nat.Prime 134499857 := by
  apply lucas_primality 134499857 (3 : ZMod 134499857)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (251, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (251, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 134499857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_107
      · exact prime_oneHundredSixtyOneFC_251
      · exact prime_oneHundredSixtyOneFC_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 134499857) ^ 67249928 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 134499857) ^ 1257008 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 134499857) ^ 535856 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 134499857) ^ 429712 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_164696333 : Nat.Prime 164696333 := by
  apply lucas_primality 164696333 (2 : ZMod 164696333)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (331, 1), (6547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (331, 1), (6547, 1)] : List FactorBlock).map factorBlockValue).prod) = 164696333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_331
      · exact prime_oneHundredSixtyOneFC_6547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 164696333) ^ 82348166 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 164696333) ^ 8668228 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 164696333) ^ 497572 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 164696333) ^ 25156 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_170216287 : Nat.Prime 170216287 := by
  apply lucas_primality 170216287 (3 : ZMod 170216287)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (233, 1), (313, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (233, 1), (313, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) = 170216287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_233
      · exact prime_oneHundredSixtyOneFC_313
      · exact prime_oneHundredSixtyOneFC_389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 170216287) ^ 85108143 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 170216287) ^ 56738762 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 170216287) ^ 730542 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 170216287) ^ 543822 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 170216287) ^ 437574 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_190157663 : Nat.Prime 190157663 := by
  apply lucas_primality 190157663 (5 : ZMod 190157663)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (5004149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (5004149, 1)] : List FactorBlock).map factorBlockValue).prod) = 190157663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_5004149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 190157663) ^ 95078831 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 190157663) ^ 10008298 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 190157663) ^ 38 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_195689519 : Nat.Prime 195689519 := by
  apply lucas_primality 195689519 (7 : ZMod 195689519)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (439, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (439, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) = 195689519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_107
      · exact prime_oneHundredSixtyOneFC_439
      · exact prime_oneHundredSixtyOneFC_2083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 195689519) ^ 97844759 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 195689519) ^ 1828874 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 195689519) ^ 445762 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 195689519) ^ 93946 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_204823961 : Nat.Prime 204823961 := by
  apply lucas_primality 204823961 (3 : ZMod 204823961)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 2), (101, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 2), (101, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 204823961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_101
      · exact prime_oneHundredSixtyOneFC_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 204823961) ^ 102411980 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 204823961) ^ 40964792 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 204823961) ^ 18620360 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 204823961) ^ 2027960 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 204823961) ^ 488840 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_206774753 : Nat.Prime 206774753 := by
  apply lucas_primality 206774753 (3 : ZMod 206774753)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (547, 1), (11813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (547, 1), (11813, 1)] : List FactorBlock).map factorBlockValue).prod) = 206774753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_547
      · exact prime_oneHundredSixtyOneFC_11813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 206774753) ^ 103387376 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 206774753) ^ 378016 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 206774753) ^ 17504 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_238341137 : Nat.Prime 238341137 := by
  apply lucas_primality 238341137 (3 : ZMod 238341137)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (47, 1), (28813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (47, 1), (28813, 1)] : List FactorBlock).map factorBlockValue).prod) = 238341137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_47
      · exact prime_oneHundredSixtyOneFC_28813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 238341137) ^ 119170568 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 238341137) ^ 21667376 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 238341137) ^ 5071088 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 238341137) ^ 8272 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_253870943 : Nat.Prime 253870943 := by
  apply lucas_primality 253870943 (5 : ZMod 253870943)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (9764267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (9764267, 1)] : List FactorBlock).map factorBlockValue).prod) = 253870943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_9764267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 253870943) ^ 126935471 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 253870943) ^ 19528534 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 253870943) ^ 26 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_263656163 : Nat.Prime 263656163 := by
  apply lucas_primality 263656163 (6 : ZMod 263656163)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (17, 1), (14387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (17, 1), (14387, 1)] : List FactorBlock).map factorBlockValue).prod) = 263656163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_14387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 263656163) ^ 131828081 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 263656163) ^ 37665166 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 263656163) ^ 23968742 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 263656163) ^ 15509186 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 263656163) ^ 18326 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_281937301 : Nat.Prime 281937301 := by
  apply lucas_primality 281937301 (6 : ZMod 281937301)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (939791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (939791, 1)] : List FactorBlock).map factorBlockValue).prod) = 281937301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_939791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 281937301) ^ 140968650 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 281937301) ^ 93979100 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 281937301) ^ 56387460 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 281937301) ^ 300 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_283340969 : Nat.Prime 283340969 := by
  apply lucas_primality 283340969 (3 : ZMod 283340969)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (53, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (53, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) = 283340969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_37
      · exact prime_oneHundredSixtyOneFC_53
      · exact prime_oneHundredSixtyOneFC_18061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 283340969) ^ 141670484 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 283340969) ^ 7657864 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 283340969) ^ 5346056 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 283340969) ^ 15688 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_290212613 : Nat.Prime 290212613 := by
  apply lucas_primality 290212613 (2 : ZMod 290212613)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (3818587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (3818587, 1)] : List FactorBlock).map factorBlockValue).prod) = 290212613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_3818587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 290212613) ^ 145106306 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 290212613) ^ 15274348 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 290212613) ^ 76 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_313850827 : Nat.Prime 313850827 := by
  apply lucas_primality 313850827 (2 : ZMod 313850827)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17436157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17436157, 1)] : List FactorBlock).map factorBlockValue).prod) = 313850827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_17436157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 313850827) ^ 156925413 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 313850827) ^ 104616942 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 313850827) ^ 18 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_360047533 : Nat.Prime 360047533 := by
  apply lucas_primality 360047533 (2 : ZMod 360047533)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (71, 1), (32507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (71, 1), (32507, 1)] : List FactorBlock).map factorBlockValue).prod) = 360047533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_71
      · exact prime_oneHundredSixtyOneFC_32507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 360047533) ^ 180023766 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 360047533) ^ 120015844 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 360047533) ^ 27695964 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 360047533) ^ 5071092 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 360047533) ^ 11076 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_361424183 : Nat.Prime 361424183 := by
  apply lucas_primality 361424183 (5 : ZMod 361424183)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (1518589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (1518589, 1)] : List FactorBlock).map factorBlockValue).prod) = 361424183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_1518589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 361424183) ^ 180712091 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 361424183) ^ 51632026 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 361424183) ^ 21260246 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 361424183) ^ 238 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_366418303 : Nat.Prime 366418303 := by
  apply lucas_primality 366418303 (3 : ZMod 366418303)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (199, 1), (306883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (199, 1), (306883, 1)] : List FactorBlock).map factorBlockValue).prod) = 366418303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_199
      · exact prime_oneHundredSixtyOneFC_306883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 366418303) ^ 183209151 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 366418303) ^ 122139434 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 366418303) ^ 1841298 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 366418303) ^ 1194 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_497797697 : Nat.Prime 497797697 := by
  apply lucas_primality 497797697 (3 : ZMod 497797697)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (11, 1), (707099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (11, 1), (707099, 1)] : List FactorBlock).map factorBlockValue).prod) = 497797697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_707099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 497797697) ^ 248898848 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 497797697) ^ 45254336 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 497797697) ^ 704 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_504116731 : Nat.Prime 504116731 := by
  apply lucas_primality 504116731 (10 : ZMod 504116731)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (13, 1), (31, 1), (41, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (13, 1), (31, 1), (41, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 504116731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 504116731) ^ 252058365 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 504116731) ^ 168038910 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 504116731) ^ 100823346 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 504116731) ^ 38778210 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 504116731) ^ 16261830 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 504116731) ^ 12295530 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 504116731) ^ 4461210 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_507741887 : Nat.Prime 507741887 := by
  apply lucas_primality 507741887 (5 : ZMod 507741887)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (253870943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (253870943, 1)] : List FactorBlock).map factorBlockValue).prod) = 507741887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_253870943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 507741887) ^ 253870943 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 507741887) ^ 2 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_544139237 : Nat.Prime 544139237 := by
  apply lucas_primality 544139237 (2 : ZMod 544139237)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (179, 1), (8539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (179, 1), (8539, 1)] : List FactorBlock).map factorBlockValue).prod) = 544139237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_89
      · exact prime_oneHundredSixtyOneFC_179
      · exact prime_oneHundredSixtyOneFC_8539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 544139237) ^ 272069618 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 544139237) ^ 6113924 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 544139237) ^ 3039884 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 544139237) ^ 63724 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_544910923 : Nat.Prime 544910923 := by
  apply lucas_primality 544910923 (2 : ZMod 544910923)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (10090943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (10090943, 1)] : List FactorBlock).map factorBlockValue).prod) = 544910923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_10090943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 544910923) ^ 272455461 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 544910923) ^ 181636974 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 544910923) ^ 54 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_561270557 : Nat.Prime 561270557 := by
  apply lucas_primality 561270557 (2 : ZMod 561270557)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (1822307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (1822307, 1)] : List FactorBlock).map factorBlockValue).prod) = 561270557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_1822307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 561270557) ^ 280635278 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 561270557) ^ 80181508 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 561270557) ^ 51024596 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 561270557) ^ 308 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_562598677 : Nat.Prime 562598677 := by
  apply lucas_primality 562598677 (5 : ZMod 562598677)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (23, 1), (293, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (23, 1), (293, 1), (773, 1)] : List FactorBlock).map factorBlockValue).prod) = 562598677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_23
      · exact prime_oneHundredSixtyOneFC_293
      · exact prime_oneHundredSixtyOneFC_773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 562598677) ^ 281299338 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 562598677) ^ 187532892 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 562598677) ^ 24460812 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 562598677) ^ 1920132 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 562598677) ^ 727812 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_588222353 : Nat.Prime 588222353 := by
  apply lucas_primality 588222353 (3 : ZMod 588222353)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (36763897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (36763897, 1)] : List FactorBlock).map factorBlockValue).prod) = 588222353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_36763897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 588222353) ^ 294111176 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 588222353) ^ 16 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_588497713 : Nat.Prime 588497713 := by
  apply lucas_primality 588497713 (5 : ZMod 588497713)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (367, 1), (3037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (367, 1), (3037, 1)] : List FactorBlock).map factorBlockValue).prod) = 588497713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_367
      · exact prime_oneHundredSixtyOneFC_3037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 588497713) ^ 294248856 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 588497713) ^ 196165904 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 588497713) ^ 53499792 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 588497713) ^ 1603536 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 588497713) ^ 193776 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_594185759 : Nat.Prime 594185759 := by
  apply lucas_primality 594185759 (13 : ZMod 594185759)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1319, 1), (225241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1319, 1), (225241, 1)] : List FactorBlock).map factorBlockValue).prod) = 594185759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_1319
      · exact prime_oneHundredSixtyOneFC_225241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 594185759) ^ 297092879 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 594185759) ^ 450482 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 594185759) ^ 2638 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_597733831 : Nat.Prime 597733831 := by
  apply lucas_primality 597733831 (3 : ZMod 597733831)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (245981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (245981, 1)] : List FactorBlock).map factorBlockValue).prod) = 597733831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_245981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 597733831) ^ 298866915 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 597733831) ^ 199244610 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 597733831) ^ 119546766 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 597733831) ^ 2430 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_698138621 : Nat.Prime 698138621 := by
  apply lucas_primality 698138621 (2 : ZMod 698138621)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (107, 1), (139, 1), (2347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (107, 1), (139, 1), (2347, 1)] : List FactorBlock).map factorBlockValue).prod) = 698138621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_107
      · exact prime_oneHundredSixtyOneFC_139
      · exact prime_oneHundredSixtyOneFC_2347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 698138621) ^ 349069310 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 698138621) ^ 139627724 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 698138621) ^ 6524660 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 698138621) ^ 5022580 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 698138621) ^ 297460 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_709874603 : Nat.Prime 709874603 := by
  apply lucas_primality 709874603 (2 : ZMod 709874603)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12457, 1), (28493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12457, 1), (28493, 1)] : List FactorBlock).map factorBlockValue).prod) = 709874603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_12457
      · exact prime_oneHundredSixtyOneFC_28493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 709874603) ^ 354937301 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 709874603) ^ 56986 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 709874603) ^ 24914 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_712885559 : Nat.Prime 712885559 := by
  apply lucas_primality 712885559 (7 : ZMod 712885559)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (4629127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (4629127, 1)] : List FactorBlock).map factorBlockValue).prod) = 712885559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_4629127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 712885559) ^ 356442779 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 712885559) ^ 101840794 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 712885559) ^ 64807778 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 712885559) ^ 154 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_17203
      · exact prime_oneHundredSixtyOneFC_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_722848367 : Nat.Prime 722848367 := by
  apply lucas_primality 722848367 (5 : ZMod 722848367)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (361424183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (361424183, 1)] : List FactorBlock).map factorBlockValue).prod) = 722848367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_361424183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 722848367) ^ 361424183 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 722848367) ^ 2 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_754596511 : Nat.Prime 754596511 := by
  apply lucas_primality 754596511 (3 : ZMod 754596511)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (53, 1), (27917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (53, 1), (27917, 1)] : List FactorBlock).map factorBlockValue).prod) = 754596511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_53
      · exact prime_oneHundredSixtyOneFC_27917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 754596511) ^ 377298255 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 754596511) ^ 251532170 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 754596511) ^ 150919302 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 754596511) ^ 44388030 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 754596511) ^ 14237670 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 754596511) ^ 27030 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_815082689 : Nat.Prime 815082689 := by
  apply lucas_primality 815082689 (3 : ZMod 815082689)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (1819381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (1819381, 1)] : List FactorBlock).map factorBlockValue).prod) = 815082689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_1819381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 815082689) ^ 407541344 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 815082689) ^ 116440384 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 815082689) ^ 448 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_834311197 : Nat.Prime 834311197 := by
  apply lucas_primality 834311197 (2 : ZMod 834311197)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (149, 1), (155539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (149, 1), (155539, 1)] : List FactorBlock).map factorBlockValue).prod) = 834311197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_149
      · exact prime_oneHundredSixtyOneFC_155539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 834311197) ^ 417155598 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 834311197) ^ 278103732 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 834311197) ^ 5599404 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 834311197) ^ 5364 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1007997181 : Nat.Prime 1007997181 := by
  apply lucas_primality 1007997181 (2 : ZMod 1007997181)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (16799953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (16799953, 1)] : List FactorBlock).map factorBlockValue).prod) = 1007997181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_16799953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1007997181) ^ 503998590 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007997181) ^ 335999060 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007997181) ^ 201599436 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007997181) ^ 60 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1132086563 : Nat.Prime 1132086563 := by
  apply lucas_primality 1132086563 (2 : ZMod 1132086563)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (907, 1), (4133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (907, 1), (4133, 1)] : List FactorBlock).map factorBlockValue).prod) = 1132086563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_151
      · exact prime_oneHundredSixtyOneFC_907
      · exact prime_oneHundredSixtyOneFC_4133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1132086563) ^ 566043281 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132086563) ^ 7497262 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132086563) ^ 1248166 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1132086563) ^ 273914 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1140261427 : Nat.Prime 1140261427 := by
  apply lucas_primality 1140261427 (3 : ZMod 1140261427)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109, 1), (581173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109, 1), (581173, 1)] : List FactorBlock).map factorBlockValue).prod) = 1140261427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_109
      · exact prime_oneHundredSixtyOneFC_581173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1140261427) ^ 570130713 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1140261427) ^ 380087142 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1140261427) ^ 10461114 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1140261427) ^ 1962 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1176444707 : Nat.Prime 1176444707 := by
  apply lucas_primality 1176444707 (2 : ZMod 1176444707)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (588222353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (588222353, 1)] : List FactorBlock).map factorBlockValue).prod) = 1176444707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_588222353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1176444707) ^ 588222353 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1176444707) ^ 2 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1426941863 : Nat.Prime 1426941863 := by
  apply lucas_primality 1426941863 (5 : ZMod 1426941863)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (3062107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (3062107, 1)] : List FactorBlock).map factorBlockValue).prod) = 1426941863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_233
      · exact prime_oneHundredSixtyOneFC_3062107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1426941863) ^ 713470931 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1426941863) ^ 6124214 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1426941863) ^ 466 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1427244191 : Nat.Prime 1427244191 := by
  apply lucas_primality 1427244191 (7 : ZMod 1427244191)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (641, 1), (222659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (641, 1), (222659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1427244191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_641
      · exact prime_oneHundredSixtyOneFC_222659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1427244191) ^ 713622095 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427244191) ^ 285448838 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427244191) ^ 2226590 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1427244191) ^ 6410 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1465673213 : Nat.Prime 1465673213 := by
  apply lucas_primality 1465673213 (2 : ZMod 1465673213)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (366418303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (366418303, 1)] : List FactorBlock).map factorBlockValue).prod) = 1465673213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_366418303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1465673213) ^ 732836606 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1465673213) ^ 4 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1498059683 : Nat.Prime 1498059683 := by
  apply lucas_primality 1498059683 (2 : ZMod 1498059683)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (257, 1), (416359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (257, 1), (416359, 1)] : List FactorBlock).map factorBlockValue).prod) = 1498059683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_257
      · exact prime_oneHundredSixtyOneFC_416359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1498059683) ^ 749029841 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1498059683) ^ 214008526 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1498059683) ^ 5829026 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1498059683) ^ 3598 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1630165379 : Nat.Prime 1630165379 := by
  apply lucas_primality 1630165379 (2 : ZMod 1630165379)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (815082689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (815082689, 1)] : List FactorBlock).map factorBlockValue).prod) = 1630165379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_815082689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1630165379) ^ 815082689 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1630165379) ^ 2 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1691623807 : Nat.Prime 1691623807 := by
  apply lucas_primality 1691623807 (3 : ZMod 1691623807)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (281937301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (281937301, 1)] : List FactorBlock).map factorBlockValue).prod) = 1691623807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_281937301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1691623807) ^ 845811903 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1691623807) ^ 563874602 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1691623807) ^ 6 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1892295113 : Nat.Prime 1892295113 := by
  apply lucas_primality 1892295113 (3 : ZMod 1892295113)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (257, 1), (920377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (257, 1), (920377, 1)] : List FactorBlock).map factorBlockValue).prod) = 1892295113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_257
      · exact prime_oneHundredSixtyOneFC_920377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1892295113) ^ 946147556 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1892295113) ^ 7363016 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1892295113) ^ 2056 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1899134921 : Nat.Prime 1899134921 := by
  apply lucas_primality 1899134921 (3 : ZMod 1899134921)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (811, 1), (58543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (811, 1), (58543, 1)] : List FactorBlock).map factorBlockValue).prod) = 1899134921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_811
      · exact prime_oneHundredSixtyOneFC_58543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1899134921) ^ 949567460 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1899134921) ^ 379826984 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1899134921) ^ 2341720 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1899134921) ^ 32440 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1999267597 : Nat.Prime 1999267597 := by
  apply lucas_primality 1999267597 (2 : ZMod 1999267597)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (6170579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (6170579, 1)] : List FactorBlock).map factorBlockValue).prod) = 1999267597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_6170579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1999267597) ^ 999633798 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1999267597) ^ 666422532 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1999267597) ^ 324 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_2260818367 : Nat.Prime 2260818367 := by
  apply lucas_primality 2260818367 (3 : ZMod 2260818367)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (79, 1), (164471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (79, 1), (164471, 1)] : List FactorBlock).map factorBlockValue).prod) = 2260818367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_29
      · exact prime_oneHundredSixtyOneFC_79
      · exact prime_oneHundredSixtyOneFC_164471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2260818367) ^ 1130409183 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2260818367) ^ 753606122 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2260818367) ^ 77959254 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2260818367) ^ 28617954 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2260818367) ^ 13746 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_2281976941 : Nat.Prime 2281976941 := by
  apply lucas_primality 2281976941 (2 : ZMod 2281976941)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (1311481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (1311481, 1)] : List FactorBlock).map factorBlockValue).prod) = 2281976941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_29
      · exact prime_oneHundredSixtyOneFC_1311481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2281976941) ^ 1140988470 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2281976941) ^ 760658980 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2281976941) ^ 456395388 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2281976941) ^ 78688860 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2281976941) ^ 1740 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_2515658779 : Nat.Prime 2515658779 := by
  apply lucas_primality 2515658779 (2 : ZMod 2515658779)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (79, 1), (1769099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (79, 1), (1769099, 1)] : List FactorBlock).map factorBlockValue).prod) = 2515658779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_79
      · exact prime_oneHundredSixtyOneFC_1769099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2515658779) ^ 1257829389 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2515658779) ^ 838552926 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2515658779) ^ 31843782 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2515658779) ^ 1422 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_2850052001 : Nat.Prime 2850052001 := by
  apply lucas_primality 2850052001 (6 : ZMod 2850052001)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 3), (107, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 3), (107, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) = 2850052001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_107
      · exact prime_oneHundredSixtyOneFC_6659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2850052001) ^ 1425026000 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 2850052001) ^ 570010400 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 2850052001) ^ 26636000 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 2850052001) ^ 428000 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3056573549 : Nat.Prime 3056573549 := by
  apply lucas_primality 3056573549 (2 : ZMod 3056573549)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (17, 1), (19, 1), (48281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (17, 1), (19, 1), (48281, 1)] : List FactorBlock).map factorBlockValue).prod) = 3056573549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_48281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3056573549) ^ 1528286774 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3056573549) ^ 436653364 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3056573549) ^ 179798444 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3056573549) ^ 160872292 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3056573549) ^ 63308 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3095557943 : Nat.Prime 3095557943 := by
  apply lucas_primality 3095557943 (5 : ZMod 3095557943)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17783, 1), (87037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17783, 1), (87037, 1)] : List FactorBlock).map factorBlockValue).prod) = 3095557943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_17783
      · exact prime_oneHundredSixtyOneFC_87037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3095557943) ^ 1547778971 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3095557943) ^ 174074 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3095557943) ^ 35566 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3332613859 : Nat.Prime 3332613859 := by
  apply lucas_primality 3332613859 (2 : ZMod 3332613859)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (127, 1), (624787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (127, 1), (624787, 1)] : List FactorBlock).map factorBlockValue).prod) = 3332613859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_127
      · exact prime_oneHundredSixtyOneFC_624787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3332613859) ^ 1666306929 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3332613859) ^ 1110871286 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3332613859) ^ 476087694 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3332613859) ^ 26241054 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3332613859) ^ 5334 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3683163173 : Nat.Prime 3683163173 := by
  apply lucas_primality 3683163173 (2 : ZMod 3683163173)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (70830061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (70830061, 1)] : List FactorBlock).map factorBlockValue).prod) = 3683163173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_70830061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3683163173) ^ 1841581586 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3683163173) ^ 283320244 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3683163173) ^ 52 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3850479811 : Nat.Prime 3850479811 := by
  apply lucas_primality 3850479811 (17 : ZMod 3850479811)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (71, 1), (613, 1), (983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (71, 1), (613, 1), (983, 1)] : List FactorBlock).map factorBlockValue).prod) = 3850479811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_71
      · exact prime_oneHundredSixtyOneFC_613
      · exact prime_oneHundredSixtyOneFC_983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 3850479811) ^ 1925239905 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (17 : ZMod 3850479811) ^ 1283493270 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (17 : ZMod 3850479811) ^ 770095962 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (17 : ZMod 3850479811) ^ 54232110 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (17 : ZMod 3850479811) ^ 6281370 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (17 : ZMod 3850479811) ^ 3917070 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_4188831727 : Nat.Prime 4188831727 := by
  apply lucas_primality 4188831727 (3 : ZMod 4188831727)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (698138621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (698138621, 1)] : List FactorBlock).map factorBlockValue).prod) = 4188831727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_698138621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4188831727) ^ 2094415863 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4188831727) ^ 1396277242 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4188831727) ^ 6 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_4540380073 : Nat.Prime 4540380073 := by
  apply lucas_primality 4540380073 (5 : ZMod 4540380073)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6277, 1), (30139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6277, 1), (30139, 1)] : List FactorBlock).map factorBlockValue).prod) = 4540380073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_6277
      · exact prime_oneHundredSixtyOneFC_30139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4540380073) ^ 2270190036 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4540380073) ^ 1513460024 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4540380073) ^ 723336 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4540380073) ^ 150648 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_4889863987 : Nat.Prime 4889863987 := by
  apply lucas_primality 4889863987 (2 : ZMod 4889863987)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (23, 1), (131, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (23, 1), (131, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) = 4889863987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_23
      · exact prime_oneHundredSixtyOneFC_131
      · exact prime_oneHundredSixtyOneFC_2273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4889863987) ^ 2444931993 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4889863987) ^ 1629954662 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4889863987) ^ 698551998 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4889863987) ^ 287639058 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4889863987) ^ 212602782 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4889863987) ^ 37327206 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4889863987) ^ 2151282 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_5592934027 : Nat.Prime 5592934027 := by
  apply lucas_primality 5592934027 (2 : ZMod 5592934027)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (1549, 1), (6917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (1549, 1), (6917, 1)] : List FactorBlock).map factorBlockValue).prod) = 5592934027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_29
      · exact prime_oneHundredSixtyOneFC_1549
      · exact prime_oneHundredSixtyOneFC_6917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5592934027) ^ 2796467013 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5592934027) ^ 1864311342 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5592934027) ^ 192859794 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5592934027) ^ 3610674 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5592934027) ^ 808578 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_5711277277 : Nat.Prime 5711277277 := by
  apply lucas_primality 5711277277 (2 : ZMod 5711277277)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (3163, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (3163, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) = 5711277277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_3163
      · exact prime_oneHundredSixtyOneFC_5573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5711277277) ^ 2855638638 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5711277277) ^ 1903759092 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5711277277) ^ 1805652 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5711277277) ^ 1024812 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_5969370107 : Nat.Prime 5969370107 := by
  apply lucas_primality 5969370107 (2 : ZMod 5969370107)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (19, 1), (31, 1), (97, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (19, 1), (31, 1), (97, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) = 5969370107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_97
      · exact prime_oneHundredSixtyOneFC_439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5969370107) ^ 2984685053 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5969370107) ^ 852767158 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5969370107) ^ 351139418 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5969370107) ^ 314177374 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5969370107) ^ 192560326 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5969370107) ^ 61539898 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5969370107) ^ 13597654 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_6386664563 : Nat.Prime 6386664563 := by
  apply lucas_primality 6386664563 (2 : ZMod 6386664563)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (44976511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (44976511, 1)] : List FactorBlock).map factorBlockValue).prod) = 6386664563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_71
      · exact prime_oneHundredSixtyOneFC_44976511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6386664563) ^ 3193332281 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6386664563) ^ 89953022 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6386664563) ^ 142 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_6393737663 : Nat.Prime 6393737663 := by
  apply lucas_primality 6393737663 (5 : ZMod 6393737663)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 6393737663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_23
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_311
      · exact prime_oneHundredSixtyOneFC_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6393737663) ^ 3196868831 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 491825974 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 277988594 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 206249602 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 20558642 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 5765318 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_7904385889 : Nat.Prime 7904385889 := by
  apply lucas_primality 7904385889 (19 : ZMod 7904385889)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (11762479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (11762479, 1)] : List FactorBlock).map factorBlockValue).prod) = 7904385889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_11762479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 7904385889) ^ 3952192944 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 7904385889) ^ 2634795296 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 7904385889) ^ 1129197984 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 7904385889) ^ 672 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_7968208013 : Nat.Prime 7968208013 := by
  apply lucas_primality 7968208013 (2 : ZMod 7968208013)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (877, 1), (2271439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (877, 1), (2271439, 1)] : List FactorBlock).map factorBlockValue).prod) = 7968208013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_877
      · exact prime_oneHundredSixtyOneFC_2271439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7968208013) ^ 3984104006 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7968208013) ^ 9085756 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7968208013) ^ 3508 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_9052809589 : Nat.Prime 9052809589 := by
  apply lucas_primality 9052809589 (2 : ZMod 9052809589)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (83822311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (83822311, 1)] : List FactorBlock).map factorBlockValue).prod) = 9052809589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_83822311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9052809589) ^ 4526404794 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9052809589) ^ 3017603196 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9052809589) ^ 108 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_9054723493 : Nat.Prime 9054723493 := by
  apply lucas_primality 9054723493 (2 : ZMod 9054723493)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (541, 1), (464917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (541, 1), (464917, 1)] : List FactorBlock).map factorBlockValue).prod) = 9054723493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_541
      · exact prime_oneHundredSixtyOneFC_464917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9054723493) ^ 4527361746 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9054723493) ^ 3018241164 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9054723493) ^ 16737012 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9054723493) ^ 19476 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_12133835171 : Nat.Prime 12133835171 := by
  apply lucas_primality 12133835171 (2 : ZMod 12133835171)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (71375501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (71375501, 1)] : List FactorBlock).map factorBlockValue).prod) = 12133835171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_71375501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12133835171) ^ 6066917585 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12133835171) ^ 2426767034 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12133835171) ^ 713755010 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12133835171) ^ 170 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_13338878633 : Nat.Prime 13338878633 := by
  apply lucas_primality 13338878633 (3 : ZMod 13338878633)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11953, 1), (139493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11953, 1), (139493, 1)] : List FactorBlock).map factorBlockValue).prod) = 13338878633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11953
      · exact prime_oneHundredSixtyOneFC_139493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 13338878633) ^ 6669439316 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13338878633) ^ 1115944 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13338878633) ^ 95624 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_16230353687 : Nat.Prime 16230353687 := by
  apply lucas_primality 16230353687 (5 : ZMod 16230353687)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (163, 1), (329711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (163, 1), (329711, 1)] : List FactorBlock).map factorBlockValue).prod) = 16230353687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_151
      · exact prime_oneHundredSixtyOneFC_163
      · exact prime_oneHundredSixtyOneFC_329711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16230353687) ^ 8115176843 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 16230353687) ^ 107485786 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 16230353687) ^ 99572722 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 16230353687) ^ 49226 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_19401299369 : Nat.Prime 19401299369 := by
  apply lucas_primality 19401299369 (3 : ZMod 19401299369)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (17, 1), (61, 1), (433, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (17, 1), (61, 1), (433, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 19401299369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_61
      · exact prime_oneHundredSixtyOneFC_433
      · exact prime_oneHundredSixtyOneFC_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19401299369) ^ 9700649684 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 19401299369) ^ 1763754488 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 19401299369) ^ 1141252904 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 19401299369) ^ 318054088 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 19401299369) ^ 44806696 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 19401299369) ^ 39513848 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_21041302453 : Nat.Prime 21041302453 := by
  apply lucas_primality 21041302453 (2 : ZMod 21041302453)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (6067, 1), (9323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (6067, 1), (9323, 1)] : List FactorBlock).map factorBlockValue).prod) = 21041302453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_6067
      · exact prime_oneHundredSixtyOneFC_9323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21041302453) ^ 10520651226 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21041302453) ^ 7013767484 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21041302453) ^ 678751692 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21041302453) ^ 3468156 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21041302453) ^ 2256924 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_22017995773 : Nat.Prime 22017995773 := by
  apply lucas_primality 22017995773 (6 : ZMod 22017995773)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (197, 1), (404951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (197, 1), (404951, 1)] : List FactorBlock).map factorBlockValue).prod) = 22017995773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_23
      · exact prime_oneHundredSixtyOneFC_197
      · exact prime_oneHundredSixtyOneFC_404951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 22017995773) ^ 11008997886 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 22017995773) ^ 7339331924 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 22017995773) ^ 957304164 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 22017995773) ^ 111766476 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 22017995773) ^ 54372 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_25036031477 : Nat.Prime 25036031477 := by
  apply lucas_primality 25036031477 (2 : ZMod 25036031477)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6883, 1), (909343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6883, 1), (909343, 1)] : List FactorBlock).map factorBlockValue).prod) = 25036031477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_6883
      · exact prime_oneHundredSixtyOneFC_909343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25036031477) ^ 12518015738 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 25036031477) ^ 3637372 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 25036031477) ^ 27532 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_26897245013 : Nat.Prime 26897245013 := by
  apply lucas_primality 26897245013 (2 : ZMod 26897245013)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (457, 2), (2927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (457, 2), (2927, 1)] : List FactorBlock).map factorBlockValue).prod) = 26897245013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_457
      · exact prime_oneHundredSixtyOneFC_2927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26897245013) ^ 13448622506 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 26897245013) ^ 2445204092 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 26897245013) ^ 58856116 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 26897245013) ^ 9189356 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_28977227353 : Nat.Prime 28977227353 := by
  apply lucas_primality 28977227353 (5 : ZMod 28977227353)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (173, 1), (2326367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (173, 1), (2326367, 1)] : List FactorBlock).map factorBlockValue).prod) = 28977227353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_173
      · exact prime_oneHundredSixtyOneFC_2326367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 28977227353) ^ 14488613676 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 28977227353) ^ 9659075784 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 28977227353) ^ 167498424 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 28977227353) ^ 12456 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_40792590343 : Nat.Prime 40792590343 := by
  apply lucas_primality 40792590343 (6 : ZMod 40792590343)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (1543, 1), (209819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (1543, 1), (209819, 1)] : List FactorBlock).map factorBlockValue).prod) = 40792590343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_1543
      · exact prime_oneHundredSixtyOneFC_209819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 40792590343) ^ 20396295171 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 40792590343) ^ 13597530114 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 40792590343) ^ 5827512906 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 40792590343) ^ 26437194 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 40792590343) ^ 194418 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_43202686297 : Nat.Prime 43202686297 := by
  apply lucas_primality 43202686297 (5 : ZMod 43202686297)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (17, 2), (41, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (17, 2), (41, 1), (1973, 1)] : List FactorBlock).map factorBlockValue).prod) = 43202686297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_1973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 43202686297) ^ 21601343148 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 43202686297) ^ 14400895432 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 43202686297) ^ 6171812328 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 43202686297) ^ 3927516936 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 43202686297) ^ 2541334488 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 43202686297) ^ 1053724056 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 43202686297) ^ 21896952 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_45103926401 : Nat.Prime 45103926401 := by
  apply lucas_primality 45103926401 (3 : ZMod 45103926401)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 2), (13, 1), (83, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 2), (13, 1), (83, 1), (13063, 1)] : List FactorBlock).map factorBlockValue).prod) = 45103926401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_83
      · exact prime_oneHundredSixtyOneFC_13063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45103926401) ^ 22551963200 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 9020785280 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 3469532800 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 543420800 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 45103926401) ^ 3452800 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_45636734023 : Nat.Prime 45636734023 := by
  apply lucas_primality 45636734023 (6 : ZMod 45636734023)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) = 45636734023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_40674451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45636734023) ^ 22818367011 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 15212244674 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 4148794002 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 2684513766 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 1122 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_49905804659 : Nat.Prime 49905804659 := by
  apply lucas_primality 49905804659 (2 : ZMod 49905804659)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (111896423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (111896423, 1)] : List FactorBlock).map factorBlockValue).prod) = 49905804659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_223
      · exact prime_oneHundredSixtyOneFC_111896423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 49905804659) ^ 24952902329 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 49905804659) ^ 223792846 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 49905804659) ^ 446 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_58074873107 : Nat.Prime 58074873107 := by
  apply lucas_primality 58074873107 (2 : ZMod 58074873107)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (18973, 1), (32563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (18973, 1), (32563, 1)] : List FactorBlock).map factorBlockValue).prod) = 58074873107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_47
      · exact prime_oneHundredSixtyOneFC_18973
      · exact prime_oneHundredSixtyOneFC_32563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58074873107) ^ 29037436553 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 58074873107) ^ 1235635598 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 58074873107) ^ 3060922 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 58074873107) ^ 1783462 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_70319855563 : Nat.Prime 70319855563 := by
  apply lucas_primality 70319855563 (2 : ZMod 70319855563)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (433, 1), (2460629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (433, 1), (2460629, 1)] : List FactorBlock).map factorBlockValue).prod) = 70319855563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_433
      · exact prime_oneHundredSixtyOneFC_2460629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70319855563) ^ 35159927781 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 70319855563) ^ 23439951854 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 70319855563) ^ 6392714142 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 70319855563) ^ 162401514 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 70319855563) ^ 28578 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_78432520189 : Nat.Prime 78432520189 := by
  apply lucas_primality 78432520189 (2 : ZMod 78432520189)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (594185759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (594185759, 1)] : List FactorBlock).map factorBlockValue).prod) = 78432520189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_594185759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 78432520189) ^ 39216260094 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 78432520189) ^ 26144173396 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 78432520189) ^ 7130229108 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 78432520189) ^ 132 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_88272264991 : Nat.Prime 88272264991 := by
  apply lucas_primality 88272264991 (7 : ZMod 88272264991)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (32334163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (32334163, 1)] : List FactorBlock).map factorBlockValue).prod) = 88272264991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_32334163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 88272264991) ^ 44136132495 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 88272264991) ^ 29424088330 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 88272264991) ^ 17654452998 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 88272264991) ^ 12610323570 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 88272264991) ^ 6790174230 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 88272264991) ^ 2730 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_89497558993 : Nat.Prime 89497558993 := by
  apply lucas_primality 89497558993 (5 : ZMod 89497558993)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (461, 1), (130469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (461, 1), (130469, 1)] : List FactorBlock).map factorBlockValue).prod) = 89497558993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_461
      · exact prime_oneHundredSixtyOneFC_130469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 89497558993) ^ 44748779496 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 89497558993) ^ 29832519664 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 89497558993) ^ 2887018032 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 89497558993) ^ 194137872 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 89497558993) ^ 685968 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_91607156309 : Nat.Prime 91607156309 := by
  apply lucas_primality 91607156309 (2 : ZMod 91607156309)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9769, 1), (2344333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9769, 1), (2344333, 1)] : List FactorBlock).map factorBlockValue).prod) = 91607156309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_9769
      · exact prime_oneHundredSixtyOneFC_2344333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 91607156309) ^ 45803578154 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 91607156309) ^ 9377332 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 91607156309) ^ 39076 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_97677135503 : Nat.Prime 97677135503 := by
  apply lucas_primality 97677135503 (5 : ZMod 97677135503)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15737, 1), (3103423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15737, 1), (3103423, 1)] : List FactorBlock).map factorBlockValue).prod) = 97677135503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_15737
      · exact prime_oneHundredSixtyOneFC_3103423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 97677135503) ^ 48838567751 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 97677135503) ^ 6206846 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 97677135503) ^ 31474 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_102802990987 : Nat.Prime 102802990987 := by
  apply lucas_primality 102802990987 (3 : ZMod 102802990987)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5711277277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5711277277, 1)] : List FactorBlock).map factorBlockValue).prod) = 102802990987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5711277277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 102802990987) ^ 51401495493 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 102802990987) ^ 34267663662 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 102802990987) ^ 18 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_104970939287 : Nat.Prime 104970939287 := by
  apply lucas_primality 104970939287 (5 : ZMod 104970939287)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (2281976941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (2281976941, 1)] : List FactorBlock).map factorBlockValue).prod) = 104970939287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_23
      · exact prime_oneHundredSixtyOneFC_2281976941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 104970939287) ^ 52485469643 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 104970939287) ^ 4563953882 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 104970939287) ^ 46 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_108628737491 : Nat.Prime 108628737491 := by
  apply lucas_primality 108628737491 (2 : ZMod 108628737491)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (13, 1), (79, 1), (215863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (13, 1), (79, 1), (215863, 1)] : List FactorBlock).map factorBlockValue).prod) = 108628737491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_79
      · exact prime_oneHundredSixtyOneFC_215863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 108628737491) ^ 54314368745 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 108628737491) ^ 21725747498 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 108628737491) ^ 15518391070 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 108628737491) ^ 8356056730 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 108628737491) ^ 1375047310 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 108628737491) ^ 503230 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_142967124779 : Nat.Prime 142967124779 := by
  apply lucas_primality 142967124779 (2 : ZMod 142967124779)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (204823961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (204823961, 1)] : List FactorBlock).map factorBlockValue).prod) = 142967124779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_349
      · exact prime_oneHundredSixtyOneFC_204823961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 142967124779) ^ 71483562389 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 142967124779) ^ 409647922 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 142967124779) ^ 698 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_155440836073 : Nat.Prime 155440836073 := by
  apply lucas_primality 155440836073 (5 : ZMod 155440836073)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) = 155440836073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_89
      · exact prime_oneHundredSixtyOneFC_373
      · exact prime_oneHundredSixtyOneFC_65033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155440836073) ^ 77720418036 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 51813612024 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 1746526248 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 416731464 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 2390184 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_158159636933 : Nat.Prime 158159636933 := by
  apply lucas_primality 158159636933 (2 : ZMod 158159636933)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (31, 1), (67, 1), (937, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (31, 1), (67, 1), (937, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) = 158159636933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_67
      · exact prime_oneHundredSixtyOneFC_937
      · exact prime_oneHundredSixtyOneFC_1847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158159636933) ^ 79079818466 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 158159636933) ^ 14378148812 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 158159636933) ^ 5101923772 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 158159636933) ^ 2360591596 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 158159636933) ^ 168793636 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 158159636933) ^ 85630556 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_173863364119 : Nat.Prime 173863364119 := by
  apply lucas_primality 173863364119 (6 : ZMod 173863364119)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (28977227353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (28977227353, 1)] : List FactorBlock).map factorBlockValue).prod) = 173863364119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_28977227353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 173863364119) ^ 86931682059 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 173863364119) ^ 57954454706 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 173863364119) ^ 6 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_203579656097 : Nat.Prime 203579656097 := by
  apply lucas_primality 203579656097 (3 : ZMod 203579656097)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (7873, 1), (47533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (7873, 1), (47533, 1)] : List FactorBlock).map factorBlockValue).prod) = 203579656097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_7873
      · exact prime_oneHundredSixtyOneFC_47533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 203579656097) ^ 101789828048 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 203579656097) ^ 11975273888 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 203579656097) ^ 25857952 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 203579656097) ^ 4282912 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_242146916549 : Nat.Prime 242146916549 := by
  apply lucas_primality 242146916549 (2 : ZMod 242146916549)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (193, 1), (6379, 1), (49171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (193, 1), (6379, 1), (49171, 1)] : List FactorBlock).map factorBlockValue).prod) = 242146916549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_193
      · exact prime_oneHundredSixtyOneFC_6379
      · exact prime_oneHundredSixtyOneFC_49171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 242146916549) ^ 121073458274 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 242146916549) ^ 1254647236 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 242146916549) ^ 37960012 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 242146916549) ^ 4924588 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_294715389733 : Nat.Prime 294715389733 := by
  apply lucas_primality 294715389733 (2 : ZMod 294715389733)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (433, 1), (3336451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (433, 1), (3336451, 1)] : List FactorBlock).map factorBlockValue).prod) = 294715389733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_433
      · exact prime_oneHundredSixtyOneFC_3336451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 294715389733) ^ 147357694866 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 294715389733) ^ 98238463244 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 294715389733) ^ 17336199396 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 294715389733) ^ 680636004 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 294715389733) ^ 88332 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_309185255989 : Nat.Prime 309185255989 := by
  apply lucas_primality 309185255989 (6 : ZMod 309185255989)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (7537, 1), (162787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (7537, 1), (162787, 1)] : List FactorBlock).map factorBlockValue).prod) = 309185255989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_7537
      · exact prime_oneHundredSixtyOneFC_162787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 309185255989) ^ 154592627994 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 103061751996 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 44169322284 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 41022324 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 309185255989) ^ 1899324 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_332218693889 : Nat.Prime 332218693889 := by
  apply lucas_primality 332218693889 (3 : ZMod 332218693889)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (463, 1), (2802871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (463, 1), (2802871, 1)] : List FactorBlock).map factorBlockValue).prod) = 332218693889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_463
      · exact prime_oneHundredSixtyOneFC_2802871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 332218693889) ^ 166109346944 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 332218693889) ^ 717534976 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 332218693889) ^ 118528 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_343588771969 : Nat.Prime 343588771969 := by
  apply lucas_primality 343588771969 (31 : ZMod 343588771969)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 343588771969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_3931
      · exact prime_oneHundredSixtyOneFC_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 343588771969) ^ 171794385984 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 114529590656 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 26429905536 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 87404928 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 19623552 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_411211963949 : Nat.Prime 411211963949 := by
  apply lucas_primality 411211963949 (2 : ZMod 411211963949)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (102802990987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (102802990987, 1)] : List FactorBlock).map factorBlockValue).prod) = 411211963949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_102802990987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 411211963949) ^ 205605981974 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 411211963949) ^ 4 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_880365989779 : Nat.Prime 880365989779 := by
  apply lucas_primality 880365989779 (3 : ZMod 880365989779)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13338878633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13338878633, 1)] : List FactorBlock).map factorBlockValue).prod) = 880365989779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_13338878633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 880365989779) ^ 440182994889 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 880365989779) ^ 293455329926 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 880365989779) ^ 80033271798 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 880365989779) ^ 66 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_902556817609 : Nat.Prime 902556817609 := by
  apply lucas_primality 902556817609 (11 : ZMod 902556817609)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73363, 1), (512609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73363, 1), (512609, 1)] : List FactorBlock).map factorBlockValue).prod) = 902556817609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_73363
      · exact prime_oneHundredSixtyOneFC_512609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 902556817609) ^ 451278408804 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 902556817609) ^ 300852272536 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 902556817609) ^ 12302616 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 902556817609) ^ 1760712 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_908514013663 : Nat.Prime 908514013663 := by
  apply lucas_primality 908514013663 (3 : ZMod 908514013663)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (2153, 1), (571783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (2153, 1), (571783, 1)] : List FactorBlock).map factorBlockValue).prod) = 908514013663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_2153
      · exact prime_oneHundredSixtyOneFC_571783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 908514013663) ^ 454257006831 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 908514013663) ^ 302838004554 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 908514013663) ^ 22158878382 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 908514013663) ^ 421975854 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 908514013663) ^ 1588914 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_991818096349 : Nat.Prime 991818096349 := by
  apply lucas_primality 991818096349 (2 : ZMod 991818096349)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (2850052001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (2850052001, 1)] : List FactorBlock).map factorBlockValue).prod) = 991818096349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_29
      · exact prime_oneHundredSixtyOneFC_2850052001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 991818096349) ^ 495909048174 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 991818096349) ^ 330606032116 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 991818096349) ^ 34200624012 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 991818096349) ^ 348 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1201015049369 : Nat.Prime 1201015049369 := by
  apply lucas_primality 1201015049369 (3 : ZMod 1201015049369)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (547, 1), (739, 1), (371387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (547, 1), (739, 1), (371387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1201015049369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_547
      · exact prime_oneHundredSixtyOneFC_739
      · exact prime_oneHundredSixtyOneFC_371387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1201015049369) ^ 600507524684 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1201015049369) ^ 2195639944 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1201015049369) ^ 1625189512 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1201015049369) ^ 3233864 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1262478147181 : Nat.Prime 1262478147181 := by
  apply lucas_primality 1262478147181 (6 : ZMod 1262478147181)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (21041302453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (21041302453, 1)] : List FactorBlock).map factorBlockValue).prod) = 1262478147181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_21041302453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1262478147181) ^ 631239073590 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1262478147181) ^ 420826049060 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1262478147181) ^ 252495629436 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1262478147181) ^ 60 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1459366549967 : Nat.Prime 1459366549967 := by
  apply lucas_primality 1459366549967 (5 : ZMod 1459366549967)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (67, 1), (179, 1), (409, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (67, 1), (179, 1), (409, 1), (11443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1459366549967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_67
      · exact prime_oneHundredSixtyOneFC_179
      · exact prime_oneHundredSixtyOneFC_409
      · exact prime_oneHundredSixtyOneFC_11443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1459366549967) ^ 729683274983 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 112258965382 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 21781590298 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 8152885754 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 3568133374 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1459366549967) ^ 127533562 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_2326461371621 : Nat.Prime 2326461371621 := by
  apply lucas_primality 2326461371621 (3 : ZMod 2326461371621)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (1181, 1), (3177271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (1181, 1), (3177271, 1)] : List FactorBlock).map factorBlockValue).prod) = 2326461371621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_1181
      · exact prime_oneHundredSixtyOneFC_3177271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2326461371621) ^ 1163230685810 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2326461371621) ^ 465292274324 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2326461371621) ^ 75047141020 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2326461371621) ^ 1969908020 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2326461371621) ^ 732220 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_2577668428667 : Nat.Prime 2577668428667 := by
  apply lucas_primality 2577668428667 (2 : ZMod 2577668428667)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4441, 1), (290212613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4441, 1), (290212613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2577668428667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_4441
      · exact prime_oneHundredSixtyOneFC_290212613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2577668428667) ^ 1288834214333 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2577668428667) ^ 580425226 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2577668428667) ^ 8882 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_2624914835707 : Nat.Prime 2624914835707 := by
  apply lucas_primality 2624914835707 (2 : ZMod 2624914835707)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (12799, 1), (833689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (12799, 1), (833689, 1)] : List FactorBlock).map factorBlockValue).prod) = 2624914835707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_12799
      · exact prime_oneHundredSixtyOneFC_833689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2624914835707) ^ 1312457417853 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2624914835707) ^ 874971611902 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2624914835707) ^ 64022313066 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2624914835707) ^ 205087494 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2624914835707) ^ 3148554 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3282280732531 : Nat.Prime 3282280732531 := by
  apply lucas_primality 3282280732531 (2 : ZMod 3282280732531)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (31, 1), (1176444707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (31, 1), (1176444707, 1)] : List FactorBlock).map factorBlockValue).prod) = 3282280732531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_1176444707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3282280732531) ^ 1641140366265 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3282280732531) ^ 1094093577510 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3282280732531) ^ 656456146506 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3282280732531) ^ 105880023630 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3282280732531) ^ 2790 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3710662694423 : Nat.Prime 3710662694423 := by
  apply lucas_primality 3710662694423 (5 : ZMod 3710662694423)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (45007, 1), (564701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (45007, 1), (564701, 1)] : List FactorBlock).map factorBlockValue).prod) = 3710662694423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_73
      · exact prime_oneHundredSixtyOneFC_45007
      · exact prime_oneHundredSixtyOneFC_564701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3710662694423) ^ 1855331347211 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3710662694423) ^ 50830995814 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3710662694423) ^ 82446346 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3710662694423) ^ 6571022 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3816841613933 : Nat.Prime 3816841613933 := by
  apply lucas_primality 3816841613933 (2 : ZMod 3816841613933)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (347, 1), (15362491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (347, 1), (15362491, 1)] : List FactorBlock).map factorBlockValue).prod) = 3816841613933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_179
      · exact prime_oneHundredSixtyOneFC_347
      · exact prime_oneHundredSixtyOneFC_15362491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3816841613933) ^ 1908420806966 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3816841613933) ^ 21323137508 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3816841613933) ^ 10999543556 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3816841613933) ^ 248452 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3888607591241 : Nat.Prime 3888607591241 := by
  apply lucas_primality 3888607591241 (3 : ZMod 3888607591241)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (43, 1), (2260818367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (43, 1), (2260818367, 1)] : List FactorBlock).map factorBlockValue).prod) = 3888607591241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_43
      · exact prime_oneHundredSixtyOneFC_2260818367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3888607591241) ^ 1944303795620 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3888607591241) ^ 777721518248 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3888607591241) ^ 90432734680 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3888607591241) ^ 1720 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_4148415406349 : Nat.Prime 4148415406349 := by
  apply lucas_primality 4148415406349 (2 : ZMod 4148415406349)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (16573, 1), (157627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (16573, 1), (157627, 1)] : List FactorBlock).map factorBlockValue).prod) = 4148415406349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_397
      · exact prime_oneHundredSixtyOneFC_16573
      · exact prime_oneHundredSixtyOneFC_157627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4148415406349) ^ 2074207703174 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4148415406349) ^ 10449409084 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4148415406349) ^ 250311676 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4148415406349) ^ 26317924 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_5875565336393 : Nat.Prime 5875565336393 := by
  apply lucas_primality 5875565336393 (3 : ZMod 5875565336393)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (43202686297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (43202686297, 1)] : List FactorBlock).map factorBlockValue).prod) = 5875565336393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_43202686297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5875565336393) ^ 2937782668196 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5875565336393) ^ 345621490376 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5875565336393) ^ 136 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_5990932437253 : Nat.Prime 5990932437253 := by
  apply lucas_primality 5990932437253 (14 : ZMod 5990932437253)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (419, 1), (170216287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (419, 1), (170216287, 1)] : List FactorBlock).map factorBlockValue).prod) = 5990932437253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_419
      · exact prime_oneHundredSixtyOneFC_170216287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 5990932437253) ^ 2995466218626 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (14 : ZMod 5990932437253) ^ 1996977479084 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (14 : ZMod 5990932437253) ^ 855847491036 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (14 : ZMod 5990932437253) ^ 14298168108 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (14 : ZMod 5990932437253) ^ 35196 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_6249904997477 : Nat.Prime 6249904997477 := by
  apply lucas_primality 6249904997477 (2 : ZMod 6249904997477)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (149, 1), (1498059683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (149, 1), (1498059683, 1)] : List FactorBlock).map factorBlockValue).prod) = 6249904997477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_149
      · exact prime_oneHundredSixtyOneFC_1498059683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6249904997477) ^ 3124952498738 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6249904997477) ^ 892843571068 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6249904997477) ^ 41945671124 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6249904997477) ^ 4172 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_6509368184021 : Nat.Prime 6509368184021 := by
  apply lucas_primality 6509368184021 (2 : ZMod 6509368184021)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (25036031477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (25036031477, 1)] : List FactorBlock).map factorBlockValue).prod) = 6509368184021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_25036031477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6509368184021) ^ 3254684092010 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6509368184021) ^ 1301873636804 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6509368184021) ^ 500720629540 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6509368184021) ^ 260 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_6904748117809 : Nat.Prime 6904748117809 := by
  apply lucas_primality 6904748117809 (7 : ZMod 6904748117809)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (46301, 1), (1035607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (46301, 1), (1035607, 1)] : List FactorBlock).map factorBlockValue).prod) = 6904748117809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_46301
      · exact prime_oneHundredSixtyOneFC_1035607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6904748117809) ^ 3452374058904 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6904748117809) ^ 2301582705936 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6904748117809) ^ 149127408 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6904748117809) ^ 6667344 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_7699082468479 : Nat.Prime 7699082468479 := by
  apply lucas_primality 7699082468479 (3 : ZMod 7699082468479)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (67, 1), (1007997181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (67, 1), (1007997181, 1)] : List FactorBlock).map factorBlockValue).prod) = 7699082468479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_67
      · exact prime_oneHundredSixtyOneFC_1007997181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7699082468479) ^ 3849541234239 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7699082468479) ^ 2566360822826 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7699082468479) ^ 405214866762 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7699082468479) ^ 114911678634 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7699082468479) ^ 7638 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_8828779222349 : Nat.Prime 8828779222349 := by
  apply lucas_primality 8828779222349 (2 : ZMod 8828779222349)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2609, 1), (10141, 1), (83423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2609, 1), (10141, 1), (83423, 1)] : List FactorBlock).map factorBlockValue).prod) = 8828779222349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_2609
      · exact prime_oneHundredSixtyOneFC_10141
      · exact prime_oneHundredSixtyOneFC_83423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8828779222349) ^ 4414389611174 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8828779222349) ^ 3383970572 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8828779222349) ^ 870602428 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8828779222349) ^ 105831476 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_9770897917097 : Nat.Prime 9770897917097 := by
  apply lucas_primality 9770897917097 (3 : ZMod 9770897917097)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (269, 1), (4540380073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (269, 1), (4540380073, 1)] : List FactorBlock).map factorBlockValue).prod) = 9770897917097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_269
      · exact prime_oneHundredSixtyOneFC_4540380073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9770897917097) ^ 4885448958548 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9770897917097) ^ 36323040584 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9770897917097) ^ 2152 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_9790001640347 : Nat.Prime 9790001640347 := by
  apply lucas_primality 9790001640347 (2 : ZMod 9790001640347)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (3049, 1), (30291409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (3049, 1), (30291409, 1)] : List FactorBlock).map factorBlockValue).prod) = 9790001640347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_53
      · exact prime_oneHundredSixtyOneFC_3049
      · exact prime_oneHundredSixtyOneFC_30291409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9790001640347) ^ 4895000820173 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9790001640347) ^ 184717012082 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9790001640347) ^ 3210889354 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9790001640347) ^ 323194 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_10382993943589 : Nat.Prime 10382993943589 := by
  apply lucas_primality 10382993943589 (13 : ZMod 10382993943589)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (19, 1), (722848367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (19, 1), (722848367, 1)] : List FactorBlock).map factorBlockValue).prod) = 10382993943589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_722848367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 10382993943589) ^ 5191496971794 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 3460997981196 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 1483284849084 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 546473365452 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 10382993943589) ^ 14364 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_11535008805553 : Nat.Prime 11535008805553 := by
  apply lucas_primality 11535008805553 (5 : ZMod 11535008805553)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (1009, 1), (12535219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (1009, 1), (12535219, 1)] : List FactorBlock).map factorBlockValue).prod) = 11535008805553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_1009
      · exact prime_oneHundredSixtyOneFC_12535219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11535008805553) ^ 5767504402776 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11535008805553) ^ 3845002935184 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11535008805553) ^ 607105726608 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11535008805553) ^ 11432119728 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11535008805553) ^ 920208 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_11727020864261 : Nat.Prime 11727020864261 := by
  apply lucas_primality 11727020864261 (2 : ZMod 11727020864261)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (45103926401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (45103926401, 1)] : List FactorBlock).map factorBlockValue).prod) = 11727020864261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_45103926401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11727020864261) ^ 5863510432130 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11727020864261) ^ 2345404172852 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11727020864261) ^ 902078528020 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11727020864261) ^ 260 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_15846587816023 : Nat.Prime 15846587816023 := by
  apply lucas_primality 15846587816023 (5 : ZMod 15846587816023)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (880365989779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (880365989779, 1)] : List FactorBlock).map factorBlockValue).prod) = 15846587816023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_880365989779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15846587816023) ^ 7923293908011 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 15846587816023) ^ 5282195938674 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 15846587816023) ^ 18 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_16326486008683 : Nat.Prime 16326486008683 := by
  apply lucas_primality 16326486008683 (3 : ZMod 16326486008683)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (677, 1), (9091, 1), (442121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (677, 1), (9091, 1), (442121, 1)] : List FactorBlock).map factorBlockValue).prod) = 16326486008683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_677
      · exact prime_oneHundredSixtyOneFC_9091
      · exact prime_oneHundredSixtyOneFC_442121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16326486008683) ^ 8163243004341 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 16326486008683) ^ 5442162002894 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 16326486008683) ^ 24115932066 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 16326486008683) ^ 1795895502 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 16326486008683) ^ 36927642 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_17160791887493 : Nat.Prime 17160791887493 := by
  apply lucas_primality 17160791887493 (2 : ZMod 17160791887493)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17160791887493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_61
      · exact prime_oneHundredSixtyOneFC_6393737663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17160791887493) ^ 8580395943746 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 1560071989772 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 281324457172 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 2684 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_19175562518401 : Nat.Prime 19175562518401 := by
  apply lucas_primality 19175562518401 (38 : ZMod 19175562518401)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 2), (479, 1), (463339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 2), (479, 1), (463339, 1)] : List FactorBlock).map factorBlockValue).prod) = 19175562518401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_479
      · exact prime_oneHundredSixtyOneFC_463339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (38 : ZMod 19175562518401) ^ 9587781259200 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 6391854172800 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 3835112503680 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 40032489600 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (38 : ZMod 19175562518401) ^ 41385600 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_21960721505683 : Nat.Prime 21960721505683 := by
  apply lucas_primality 21960721505683 (2 : ZMod 21960721505683)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (61, 1), (22433, 1), (297191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (61, 1), (22433, 1), (297191, 1)] : List FactorBlock).map factorBlockValue).prod) = 21960721505683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_61
      · exact prime_oneHundredSixtyOneFC_22433
      · exact prime_oneHundredSixtyOneFC_297191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21960721505683) ^ 10980360752841 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21960721505683) ^ 7320240501894 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21960721505683) ^ 360011827962 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21960721505683) ^ 978947154 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21960721505683) ^ 73894302 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_22333016010577 : Nat.Prime 22333016010577 := by
  apply lucas_primality 22333016010577 (5 : ZMod 22333016010577)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (479, 1), (3701, 1), (11411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (479, 1), (3701, 1), (11411, 1)] : List FactorBlock).map factorBlockValue).prod) = 22333016010577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_23
      · exact prime_oneHundredSixtyOneFC_479
      · exact prime_oneHundredSixtyOneFC_3701
      · exact prime_oneHundredSixtyOneFC_11411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 22333016010577) ^ 11166508005288 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 22333016010577) ^ 7444338670192 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 22333016010577) ^ 971000696112 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 22333016010577) ^ 46624250544 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 22333016010577) ^ 6034319376 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 22333016010577) ^ 1957148016 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_30712228800887 : Nat.Prime 30712228800887 := by
  apply lucas_primality 30712228800887 (5 : ZMod 30712228800887)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (743, 1), (1171, 1), (17649631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (743, 1), (1171, 1), (17649631, 1)] : List FactorBlock).map factorBlockValue).prod) = 30712228800887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_743
      · exact prime_oneHundredSixtyOneFC_1171
      · exact prime_oneHundredSixtyOneFC_17649631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 30712228800887) ^ 15356114400443 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 30712228800887) ^ 41335435802 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 30712228800887) ^ 26227351666 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 30712228800887) ^ 1740106 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_33763383185377 : Nat.Prime 33763383185377 := by
  apply lucas_primality 33763383185377 (11 : ZMod 33763383185377)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (47, 1), (137, 1), (4201583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (47, 1), (137, 1), (4201583, 1)] : List FactorBlock).map factorBlockValue).prod) = 33763383185377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_47
      · exact prime_oneHundredSixtyOneFC_137
      · exact prime_oneHundredSixtyOneFC_4201583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 33763383185377) ^ 16881691592688 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 11254461061792 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 2597183321952 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 718369855008 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 246448052448 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 33763383185377) ^ 8035872 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_37349493207721 : Nat.Prime 37349493207721 := by
  apply lucas_primality 37349493207721 (13 : ZMod 37349493207721)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (613, 1), (507741887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (613, 1), (507741887, 1)] : List FactorBlock).map factorBlockValue).prod) = 37349493207721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_613
      · exact prime_oneHundredSixtyOneFC_507741887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 37349493207721) ^ 18674746603860 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 37349493207721) ^ 12449831069240 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 37349493207721) ^ 7469898641544 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 37349493207721) ^ 60929026440 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 37349493207721) ^ 73560 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_67132559769439 : Nat.Prime 67132559769439 := by
  apply lucas_primality 67132559769439 (3 : ZMod 67132559769439)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (108628737491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (108628737491, 1)] : List FactorBlock).map factorBlockValue).prod) = 67132559769439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_103
      · exact prime_oneHundredSixtyOneFC_108628737491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 67132559769439) ^ 33566279884719 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 67132559769439) ^ 22377519923146 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 67132559769439) ^ 651772424946 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 67132559769439) ^ 618 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_82055317465903 : Nat.Prime 82055317465903 := by
  apply lucas_primality 82055317465903 (10 : ZMod 82055317465903)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 2), (251, 1), (13720877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 2), (251, 1), (13720877, 1)] : List FactorBlock).map factorBlockValue).prod) = 82055317465903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_251
      · exact prime_oneHundredSixtyOneFC_13720877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 82055317465903) ^ 41027658732951 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 82055317465903) ^ 27351772488634 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 82055317465903) ^ 7459574315082 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 82055317465903) ^ 4318700919258 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 82055317465903) ^ 326913615402 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 82055317465903) ^ 5980326 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_211729285236823 : Nat.Prime 211729285236823 := by
  apply lucas_primality 211729285236823 (6 : ZMod 211729285236823)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (113501, 1), (3493333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (113501, 1), (3493333, 1)] : List FactorBlock).map factorBlockValue).prod) = 211729285236823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_89
      · exact prime_oneHundredSixtyOneFC_113501
      · exact prime_oneHundredSixtyOneFC_3493333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 211729285236823) ^ 105864642618411 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 211729285236823) ^ 70576428412274 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 211729285236823) ^ 2378980732998 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 211729285236823) ^ 1865439822 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 211729285236823) ^ 60609534 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_223330160105771 : Nat.Prime 223330160105771 := by
  apply lucas_primality 223330160105771 (2 : ZMod 223330160105771)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (22333016010577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (22333016010577, 1)] : List FactorBlock).map factorBlockValue).prod) = 223330160105771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_22333016010577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 223330160105771) ^ 111665080052885 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 223330160105771) ^ 44666032021154 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 223330160105771) ^ 10 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_227119755515941 : Nat.Prime 227119755515941 := by
  apply lucas_primality 227119755515941 (6 : ZMod 227119755515941)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (7, 1), (277, 1), (1063, 1), (612169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (7, 1), (277, 1), (1063, 1), (612169, 1)] : List FactorBlock).map factorBlockValue).prod) = 227119755515941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_277
      · exact prime_oneHundredSixtyOneFC_1063
      · exact prime_oneHundredSixtyOneFC_612169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 227119755515941) ^ 113559877757970 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 227119755515941) ^ 75706585171980 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 227119755515941) ^ 45423951103188 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 227119755515941) ^ 32445679359420 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 227119755515941) ^ 819926915220 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 227119755515941) ^ 213659224380 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 227119755515941) ^ 371008260 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_255252382923991 : Nat.Prime 255252382923991 := by
  apply lucas_primality 255252382923991 (3 : ZMod 255252382923991)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1514033, 1), (5619701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1514033, 1), (5619701, 1)] : List FactorBlock).map factorBlockValue).prod) = 255252382923991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_1514033
      · exact prime_oneHundredSixtyOneFC_5619701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 255252382923991) ^ 127626191461995 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 255252382923991) ^ 85084127641330 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 255252382923991) ^ 51050476584798 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 255252382923991) ^ 168591030 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 255252382923991) ^ 45420990 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_287365314175127 : Nat.Prime 287365314175127 := by
  apply lucas_primality 287365314175127 (5 : ZMod 287365314175127)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23971, 1), (544910923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23971, 1), (544910923, 1)] : List FactorBlock).map factorBlockValue).prod) = 287365314175127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_23971
      · exact prime_oneHundredSixtyOneFC_544910923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 287365314175127) ^ 143682657087563 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 287365314175127) ^ 26124119470466 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 287365314175127) ^ 11988040306 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 287365314175127) ^ 527362 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_309190355008889 : Nat.Prime 309190355008889 := by
  apply lucas_primality 309190355008889 (3 : ZMod 309190355008889)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (3847, 1), (164696333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (3847, 1), (164696333, 1)] : List FactorBlock).map factorBlockValue).prod) = 309190355008889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_61
      · exact prime_oneHundredSixtyOneFC_3847
      · exact prime_oneHundredSixtyOneFC_164696333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 309190355008889) ^ 154595177504444 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 309190355008889) ^ 5068694344408 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 309190355008889) ^ 80371810504 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 309190355008889) ^ 1877336 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_312636878054861 : Nat.Prime 312636878054861 := by
  apply lucas_primality 312636878054861 (3 : ZMod 312636878054861)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13709, 1), (1140261427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13709, 1), (1140261427, 1)] : List FactorBlock).map factorBlockValue).prod) = 312636878054861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_13709
      · exact prime_oneHundredSixtyOneFC_1140261427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 312636878054861) ^ 156318439027430 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 312636878054861) ^ 62527375610972 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 312636878054861) ^ 22805228540 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 312636878054861) ^ 274180 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_352533920183581 : Nat.Prime 352533920183581 := by
  apply lucas_primality 352533920183581 (7 : ZMod 352533920183581)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (5875565336393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (5875565336393, 1)] : List FactorBlock).map factorBlockValue).prod) = 352533920183581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_5875565336393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 352533920183581) ^ 176266960091790 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 352533920183581) ^ 117511306727860 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 352533920183581) ^ 70506784036716 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 352533920183581) ^ 60 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_357725604662743 : Nat.Prime 357725604662743 := by
  apply lucas_primality 357725604662743 (5 : ZMod 357725604662743)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (193, 1), (349, 1), (28553171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (193, 1), (349, 1), (28553171, 1)] : List FactorBlock).map factorBlockValue).prod) = 357725604662743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_193
      · exact prime_oneHundredSixtyOneFC_349
      · exact prime_oneHundredSixtyOneFC_28553171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 357725604662743) ^ 178862802331371 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 357725604662743) ^ 119241868220914 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 357725604662743) ^ 11539535634282 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 357725604662743) ^ 1853500542294 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 357725604662743) ^ 1025001732558 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 357725604662743) ^ 12528402 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_497782709415311 : Nat.Prime 497782709415311 := by
  apply lucas_primality 497782709415311 (19 : ZMod 497782709415311)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (157, 1), (683, 1), (2423, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (157, 1), (683, 1), (2423, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) = 497782709415311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_157
      · exact prime_oneHundredSixtyOneFC_683
      · exact prime_oneHundredSixtyOneFC_2423
      · exact prime_oneHundredSixtyOneFC_17417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 497782709415311) ^ 248891354707655 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 497782709415311) ^ 99556541883062 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 497782709415311) ^ 45252973583210 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 497782709415311) ^ 3170590505830 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 497782709415311) ^ 728818022570 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 497782709415311) ^ 205440655970 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (19 : ZMod 497782709415311) ^ 28580278430 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_549550093265597 : Nat.Prime 549550093265597 := by
  apply lucas_primality 549550093265597 (2 : ZMod 549550093265597)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (200909, 1), (16678771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (200909, 1), (16678771, 1)] : List FactorBlock).map factorBlockValue).prod) = 549550093265597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_200909
      · exact prime_oneHundredSixtyOneFC_16678771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 549550093265597) ^ 274775046632798 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 549550093265597) ^ 13403660811356 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 549550093265597) ^ 2735318444 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 549550093265597) ^ 32949076 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_600861013022771 : Nat.Prime 600861013022771 := by
  apply lucas_primality 600861013022771 (2 : ZMod 600861013022771)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (106801, 1), (562598677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (106801, 1), (562598677, 1)] : List FactorBlock).map factorBlockValue).prod) = 600861013022771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_106801
      · exact prime_oneHundredSixtyOneFC_562598677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 600861013022771) ^ 300430506511385 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 600861013022771) ^ 120172202604554 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 600861013022771) ^ 5625986770 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 600861013022771) ^ 1068010 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_605401060944023 : Nat.Prime 605401060944023 := by
  apply lucas_primality 605401060944023 (5 : ZMod 605401060944023)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) = 605401060944023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_701
      · exact prime_oneHundredSixtyOneFC_9769
      · exact prime_oneHundredSixtyOneFC_6314617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 605401060944023) ^ 302700530472011 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 86485865849146 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 863624908622 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 61971651238 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 95872966 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_805373625772843 : Nat.Prime 805373625772843 := by
  apply lucas_primality 805373625772843 (2 : ZMod 805373625772843)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19175562518401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19175562518401, 1)] : List FactorBlock).map factorBlockValue).prod) = 805373625772843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_19175562518401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 805373625772843) ^ 402686812886421 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 805373625772843) ^ 268457875257614 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 805373625772843) ^ 115053375110406 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 805373625772843) ^ 42 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_824517412163923 : Nat.Prime 824517412163923 := by
  apply lucas_primality 824517412163923 (3 : ZMod 824517412163923)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1170581, 1), (117394327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1170581, 1), (117394327, 1)] : List FactorBlock).map factorBlockValue).prod) = 824517412163923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_1170581
      · exact prime_oneHundredSixtyOneFC_117394327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 824517412163923) ^ 412258706081961 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 824517412163923) ^ 274839137387974 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 824517412163923) ^ 704365962 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 824517412163923) ^ 7023486 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1162290630024259 : Nat.Prime 1162290630024259 := by
  apply lucas_primality 1162290630024259 (10 : ZMod 1162290630024259)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (151, 1), (7968208013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (151, 1), (7968208013, 1)] : List FactorBlock).map factorBlockValue).prod) = 1162290630024259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_23
      · exact prime_oneHundredSixtyOneFC_151
      · exact prime_oneHundredSixtyOneFC_7968208013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1162290630024259) ^ 581145315012129 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 1162290630024259) ^ 387430210008086 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 1162290630024259) ^ 166041518574894 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 1162290630024259) ^ 50534375218446 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 1162290630024259) ^ 7697288940558 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 1162290630024259) ^ 145866 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1178678698592519 : Nat.Prime 1178678698592519 := by
  apply lucas_primality 1178678698592519 (11 : ZMod 1178678698592519)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (773, 1), (1013, 1), (8456419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (773, 1), (1013, 1), (8456419, 1)] : List FactorBlock).map factorBlockValue).prod) = 1178678698592519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_89
      · exact prime_oneHundredSixtyOneFC_773
      · exact prime_oneHundredSixtyOneFC_1013
      · exact prime_oneHundredSixtyOneFC_8456419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1178678698592519) ^ 589339349296259 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1178678698592519) ^ 13243580883062 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1178678698592519) ^ 1524810735566 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1178678698592519) ^ 1163552515886 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 1178678698592519) ^ 139382722 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1753150017128941 : Nat.Prime 1753150017128941 := by
  apply lucas_primality 1753150017128941 (6 : ZMod 1753150017128941)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (41, 1), (53, 1), (263656163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (41, 1), (53, 1), (263656163, 1)] : List FactorBlock).map factorBlockValue).prod) = 1753150017128941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_53
      · exact prime_oneHundredSixtyOneFC_263656163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1753150017128941) ^ 876575008564470 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1753150017128941) ^ 584383339042980 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1753150017128941) ^ 350630003425788 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1753150017128941) ^ 103126471595820 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1753150017128941) ^ 42759756515340 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1753150017128941) ^ 33078302209980 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1753150017128941) ^ 6649380 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1869370107385603 : Nat.Prime 1869370107385603 := by
  apply lucas_primality 1869370107385603 (2 : ZMod 1869370107385603)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5680691, 1), (54845737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5680691, 1), (54845737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1869370107385603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5680691
      · exact prime_oneHundredSixtyOneFC_54845737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1869370107385603) ^ 934685053692801 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1869370107385603) ^ 623123369128534 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1869370107385603) ^ 329074422 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1869370107385603) ^ 34084146 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_2274443180374681 : Nat.Prime 2274443180374681 := by
  apply lucas_primality 2274443180374681 (22 : ZMod 2274443180374681)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (902556817609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (902556817609, 1)] : List FactorBlock).map factorBlockValue).prod) = 2274443180374681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_902556817609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 2274443180374681) ^ 1137221590187340 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (22 : ZMod 2274443180374681) ^ 758147726791560 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (22 : ZMod 2274443180374681) ^ 454888636074936 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (22 : ZMod 2274443180374681) ^ 324920454339240 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (22 : ZMod 2274443180374681) ^ 2520 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3374087986716773 : Nat.Prime 3374087986716773 := by
  apply lucas_primality 3374087986716773 (2 : ZMod 3374087986716773)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (3816841613933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (3816841613933, 1)] : List FactorBlock).map factorBlockValue).prod) = 3374087986716773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_3816841613933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3374087986716773) ^ 1687043993358386 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3374087986716773) ^ 259545229747444 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3374087986716773) ^ 198475763924516 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3374087986716773) ^ 884 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_6748175973433547 : Nat.Prime 6748175973433547 := by
  apply lucas_primality 6748175973433547 (2 : ZMod 6748175973433547)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3374087986716773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3374087986716773, 1)] : List FactorBlock).map factorBlockValue).prod) = 6748175973433547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3374087986716773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6748175973433547) ^ 3374087986716773 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6748175973433547) ^ 2 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_7203943048028777 : Nat.Prime 7203943048028777 := by
  apply lucas_primality 7203943048028777 (3 : ZMod 7203943048028777)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (53, 1), (659, 1), (3683163173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (53, 1), (659, 1), (3683163173, 1)] : List FactorBlock).map factorBlockValue).prod) = 7203943048028777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_53
      · exact prime_oneHundredSixtyOneFC_659
      · exact prime_oneHundredSixtyOneFC_3683163173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7203943048028777) ^ 3601971524014388 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7203943048028777) ^ 1029134721146968 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7203943048028777) ^ 135923453736392 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7203943048028777) ^ 10931628297464 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7203943048028777) ^ 1955912 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_7455929975633927 : Nat.Prime 7455929975633927 := by
  apply lucas_primality 7455929975633927 (5 : ZMod 7455929975633927)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (193, 1), (81043, 1), (238341137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (193, 1), (81043, 1), (238341137, 1)] : List FactorBlock).map factorBlockValue).prod) = 7455929975633927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_193
      · exact prime_oneHundredSixtyOneFC_81043
      · exact prime_oneHundredSixtyOneFC_238341137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7455929975633927) ^ 3727964987816963 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 7455929975633927) ^ 38631761531782 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 7455929975633927) ^ 91999678882 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 7455929975633927) ^ 31282598 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_9665279717140337 : Nat.Prime 9665279717140337 := by
  apply lucas_primality 9665279717140337 (3 : ZMod 9665279717140337)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (16326486008683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (16326486008683, 1)] : List FactorBlock).map factorBlockValue).prod) = 9665279717140337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_37
      · exact prime_oneHundredSixtyOneFC_16326486008683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9665279717140337) ^ 4832639858570168 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9665279717140337) ^ 261223776138928 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9665279717140337) ^ 592 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_11278270041265753 : Nat.Prime 11278270041265753 := by
  apply lucas_primality 11278270041265753 (5 : ZMod 11278270041265753)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (67132559769439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (67132559769439, 1)] : List FactorBlock).map factorBlockValue).prod) = 11278270041265753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_67132559769439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11278270041265753) ^ 5639135020632876 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11278270041265753) ^ 3759423347088584 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11278270041265753) ^ 1611181434466536 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11278270041265753) ^ 168 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_12403446782176607 : Nat.Prime 12403446782176607 := by
  apply lucas_primality 12403446782176607 (5 : ZMod 12403446782176607)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (31, 2), (89, 1), (1877, 1), (2971607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (31, 2), (89, 1), (1877, 1), (2971607, 1)] : List FactorBlock).map factorBlockValue).prod) = 12403446782176607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_89
      · exact prime_oneHundredSixtyOneFC_1877
      · exact prime_oneHundredSixtyOneFC_2971607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12403446782176607) ^ 6201723391088303 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12403446782176607) ^ 954111290936662 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12403446782176607) ^ 400111186521826 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12403446782176607) ^ 139364570586254 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12403446782176607) ^ 6608122952678 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12403446782176607) ^ 4173986258 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_16501501780295267 : Nat.Prime 16501501780295267 := by
  apply lucas_primality 16501501780295267 (2 : ZMod 16501501780295267)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1178678698592519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1178678698592519, 1)] : List FactorBlock).map factorBlockValue).prod) = 16501501780295267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_1178678698592519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16501501780295267) ^ 8250750890147633 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 16501501780295267) ^ 2357357397185038 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 16501501780295267) ^ 14 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_20454344381390743 : Nat.Prime 20454344381390743 := by
  apply lucas_primality 20454344381390743 (3 : ZMod 20454344381390743)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (30712228800887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (30712228800887, 1)] : List FactorBlock).map factorBlockValue).prod) = 20454344381390743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_37
      · exact prime_oneHundredSixtyOneFC_30712228800887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20454344381390743) ^ 10227172190695371 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 20454344381390743) ^ 6818114793796914 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 20454344381390743) ^ 552820118415966 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 20454344381390743) ^ 666 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_25331661784814219 : Nat.Prime 25331661784814219 := by
  apply lucas_primality 25331661784814219 (2 : ZMod 25331661784814219)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (7669967, 1), (9545399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (7669967, 1), (9545399, 1)] : List FactorBlock).map factorBlockValue).prod) = 25331661784814219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_173
      · exact prime_oneHundredSixtyOneFC_7669967
      · exact prime_oneHundredSixtyOneFC_9545399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25331661784814219) ^ 12665830892407109 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 25331661784814219) ^ 146425790663666 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 25331661784814219) ^ 3302708054 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 25331661784814219) ^ 2653808582 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_26247568522222639 : Nat.Prime 26247568522222639 := by
  apply lucas_primality 26247568522222639 (6 : ZMod 26247568522222639)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (241, 1), (2063, 1), (4751, 1), (617327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (241, 1), (2063, 1), (4751, 1), (617327, 1)] : List FactorBlock).map factorBlockValue).prod) = 26247568522222639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_241
      · exact prime_oneHundredSixtyOneFC_2063
      · exact prime_oneHundredSixtyOneFC_4751
      · exact prime_oneHundredSixtyOneFC_617327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 26247568522222639) ^ 13123784261111319 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 26247568522222639) ^ 8749189507407546 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 26247568522222639) ^ 108911072706318 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 26247568522222639) ^ 12723009463026 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 26247568522222639) ^ 5524640817138 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (6 : ZMod 26247568522222639) ^ 42518095794 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_27381370965110893 : Nat.Prime 27381370965110893 := by
  apply lucas_primality 27381370965110893 (2 : ZMod 27381370965110893)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (6122287, 1), (124233581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (6122287, 1), (124233581, 1)] : List FactorBlock).map factorBlockValue).prod) = 27381370965110893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_6122287
      · exact prime_oneHundredSixtyOneFC_124233581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27381370965110893) ^ 13690685482555446 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27381370965110893) ^ 9127123655036964 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27381370965110893) ^ 4472408916 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27381370965110893) ^ 220402332 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_40345144749671933 : Nat.Prime 40345144749671933 := by
  apply lucas_primality 40345144749671933 (2 : ZMod 40345144749671933)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (46477, 1), (3056573549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (46477, 1), (3056573549, 1)] : List FactorBlock).map factorBlockValue).prod) = 40345144749671933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_71
      · exact prime_oneHundredSixtyOneFC_46477
      · exact prime_oneHundredSixtyOneFC_3056573549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40345144749671933) ^ 20172572374835966 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 40345144749671933) ^ 568241475347492 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 40345144749671933) ^ 868066887916 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 40345144749671933) ^ 13199468 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_42392374596668051 : Nat.Prime 42392374596668051 := by
  apply lucas_primality 42392374596668051 (2 : ZMod 42392374596668051)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (19, 1), (2624914835707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (19, 1), (2624914835707, 1)] : List FactorBlock).map factorBlockValue).prod) = 42392374596668051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_2624914835707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42392374596668051) ^ 21196187298334025 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42392374596668051) ^ 8478474919333610 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42392374596668051) ^ 2493669093921650 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42392374596668051) ^ 2231177610350950 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42392374596668051) ^ 16150 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_53241274286720537 : Nat.Prime 53241274286720537 := by
  apply lucas_primality 53241274286720537 (3 : ZMod 53241274286720537)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) = 53241274286720537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_145829
      · exact prime_oneHundredSixtyOneFC_45636734023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53241274286720537) ^ 26620637143360268 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 365093872184 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 1166632 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_65538369885629057 : Nat.Prime 65538369885629057 := by
  apply lucas_primality 65538369885629057 (3 : ZMod 65538369885629057)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (13, 1), (59, 1), (1019, 1), (14149, 1), (46301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (13, 1), (59, 1), (1019, 1), (14149, 1), (46301, 1)] : List FactorBlock).map factorBlockValue).prod) = 65538369885629057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_59
      · exact prime_oneHundredSixtyOneFC_1019
      · exact prime_oneHundredSixtyOneFC_14149
      · exact prime_oneHundredSixtyOneFC_46301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65538369885629057) ^ 32769184942814528 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 65538369885629057) ^ 5041413068125312 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 65538369885629057) ^ 1110819828569984 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 65538369885629057) ^ 64316359063424 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 65538369885629057) ^ 4632014268544 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 65538369885629057) ^ 1415484976256 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_68233295411240431 : Nat.Prime 68233295411240431 := by
  apply lucas_primality 68233295411240431 (15 : ZMod 68233295411240431)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2274443180374681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2274443180374681, 1)] : List FactorBlock).map factorBlockValue).prod) = 68233295411240431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_2274443180374681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 68233295411240431) ^ 34116647705620215 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (15 : ZMod 68233295411240431) ^ 22744431803746810 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (15 : ZMod 68233295411240431) ^ 13646659082248086 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (15 : ZMod 68233295411240431) ^ 30 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_84784749193336103 : Nat.Prime 84784749193336103 := by
  apply lucas_primality 84784749193336103 (5 : ZMod 84784749193336103)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42392374596668051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42392374596668051, 1)] : List FactorBlock).map factorBlockValue).prod) = 84784749193336103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_42392374596668051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 84784749193336103) ^ 42392374596668051 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 84784749193336103) ^ 2 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_92077365910501919 : Nat.Prime 92077365910501919 := by
  apply lucas_primality 92077365910501919 (37 : ZMod 92077365910501919)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (887, 1), (12391, 1), (4188831727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (887, 1), (12391, 1), (4188831727, 1)] : List FactorBlock).map factorBlockValue).prod) = 92077365910501919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_887
      · exact prime_oneHundredSixtyOneFC_12391
      · exact prime_oneHundredSixtyOneFC_4188831727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (37 : ZMod 92077365910501919) ^ 46038682955250959 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (37 : ZMod 92077365910501919) ^ 103807627858514 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (37 : ZMod 92077365910501919) ^ 7430987483698 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (37 : ZMod 92077365910501919) ^ 21981634 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_104990274088890557 : Nat.Prime 104990274088890557 := by
  apply lucas_primality 104990274088890557 (2 : ZMod 104990274088890557)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (26247568522222639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (26247568522222639, 1)] : List FactorBlock).map factorBlockValue).prod) = 104990274088890557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_26247568522222639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 104990274088890557) ^ 52495137044445278 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 104990274088890557) ^ 4 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_114969019264351177 : Nat.Prime 114969019264351177 := by
  apply lucas_primality 114969019264351177 (10 : ZMod 114969019264351177)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (195469, 1), (597733831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (195469, 1), (597733831, 1)] : List FactorBlock).map factorBlockValue).prod) = 114969019264351177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_195469
      · exact prime_oneHundredSixtyOneFC_597733831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 114969019264351177) ^ 57484509632175588 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 38323006421450392 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 2804122421081736 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 588170089704 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 114969019264351177) ^ 192341496 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_135985957393556749 : Nat.Prime 135985957393556749 := by
  apply lucas_primality 135985957393556749 (2 : ZMod 135985957393556749)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (223, 1), (2447, 1), (561270557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (223, 1), (2447, 1), (561270557, 1)] : List FactorBlock).map factorBlockValue).prod) = 135985957393556749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_37
      · exact prime_oneHundredSixtyOneFC_223
      · exact prime_oneHundredSixtyOneFC_2447
      · exact prime_oneHundredSixtyOneFC_561270557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135985957393556749) ^ 67992978696778374 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 45328652464518916 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 3675296145771804 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 609802499522676 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 55572520389684 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 135985957393556749) ^ 242282364 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_165716899991283989 : Nat.Prime 165716899991283989 := by
  apply lucas_primality 165716899991283989 (2 : ZMod 165716899991283989)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (1218953, 1), (1999267597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (1218953, 1), (1999267597, 1)] : List FactorBlock).map factorBlockValue).prod) = 165716899991283989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_1218953
      · exact prime_oneHundredSixtyOneFC_1999267597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 165716899991283989) ^ 82858449995641994 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 165716899991283989) ^ 9748052940663764 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 165716899991283989) ^ 135950196596 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 165716899991283989) ^ 82888804 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_169569498386672207 : Nat.Prime 169569498386672207 := by
  apply lucas_primality 169569498386672207 (5 : ZMod 169569498386672207)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (84784749193336103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (84784749193336103, 1)] : List FactorBlock).map factorBlockValue).prod) = 169569498386672207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_84784749193336103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 169569498386672207) ^ 84784749193336103 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 169569498386672207) ^ 2 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_248068935643532141 : Nat.Prime 248068935643532141 := by
  apply lucas_primality 248068935643532141 (2 : ZMod 248068935643532141)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (12403446782176607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (12403446782176607, 1)] : List FactorBlock).map factorBlockValue).prod) = 248068935643532141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_12403446782176607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 248068935643532141) ^ 124034467821766070 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 248068935643532141) ^ 49613787128706428 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 248068935643532141) ^ 20 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_261318517715367989 : Nat.Prime 261318517715367989 := by
  apply lucas_primality 261318517715367989 (2 : ZMod 261318517715367989)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (997, 1), (1481, 1), (1427244191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (997, 1), (1481, 1), (1427244191, 1)] : List FactorBlock).map factorBlockValue).prod) = 261318517715367989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_997
      · exact prime_oneHundredSixtyOneFC_1481
      · exact prime_oneHundredSixtyOneFC_1427244191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 261318517715367989) ^ 130659258857683994 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 8429629603721548 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 262104832212004 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 176447344844948 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 261318517715367989) ^ 183093068 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_284075963654540713 : Nat.Prime 284075963654540713 := by
  apply lucas_primality 284075963654540713 (7 : ZMod 284075963654540713)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (53, 1), (223330160105771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (53, 1), (223330160105771, 1)] : List FactorBlock).map factorBlockValue).prod) = 284075963654540713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_53
      · exact prime_oneHundredSixtyOneFC_223330160105771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 284075963654540713) ^ 142037981827270356 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 284075963654540713) ^ 94691987884846904 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 284075963654540713) ^ 5359923842538504 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 284075963654540713) ^ 1272 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_305185311208195361 : Nat.Prime 305185311208195361 := by
  apply lucas_primality 305185311208195361 (3 : ZMod 305185311208195361)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (71, 1), (141277, 1), (190157663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (71, 1), (141277, 1), (190157663, 1)] : List FactorBlock).map factorBlockValue).prod) = 305185311208195361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_71
      · exact prime_oneHundredSixtyOneFC_141277
      · exact prime_oneHundredSixtyOneFC_190157663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 305185311208195361) ^ 152592655604097680 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 61037062241639072 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 4298384664904160 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 2160191051680 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 305185311208195361) ^ 1604906720 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_365779902132199649 : Nat.Prime 365779902132199649 := by
  apply lucas_primality 365779902132199649 (3 : ZMod 365779902132199649)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (89, 1), (499, 1), (157007, 1), (1639307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (89, 1), (499, 1), (157007, 1), (1639307, 1)] : List FactorBlock).map factorBlockValue).prod) = 365779902132199649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_89
      · exact prime_oneHundredSixtyOneFC_499
      · exact prime_oneHundredSixtyOneFC_157007
      · exact prime_oneHundredSixtyOneFC_1639307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 365779902132199649) ^ 182889951066099824 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 365779902132199649) ^ 4109886540811232 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 365779902132199649) ^ 733025855976352 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 365779902132199649) ^ 2329704421664 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 365779902132199649) ^ 223130812064 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1203499021821786587 : Nat.Prime 1203499021821786587 := by
  apply lucas_primality 1203499021821786587 (2 : ZMod 1203499021821786587)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (7754323, 1), (5969370107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (7754323, 1), (5969370107, 1)] : List FactorBlock).map factorBlockValue).prod) = 1203499021821786587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_7754323
      · exact prime_oneHundredSixtyOneFC_5969370107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1203499021821786587) ^ 601749510910893293 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203499021821786587) ^ 92576847832445122 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203499021821786587) ^ 155203622782 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1203499021821786587) ^ 201612398 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1310025757004245097 : Nat.Prime 1310025757004245097 := by
  apply lucas_primality 1310025757004245097 (3 : ZMod 1310025757004245097)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (41, 1), (131, 1), (1481, 1), (709874603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (41, 1), (131, 1), (1481, 1), (709874603, 1)] : List FactorBlock).map factorBlockValue).prod) = 1310025757004245097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_29
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_131
      · exact prime_oneHundredSixtyOneFC_1481
      · exact prime_oneHundredSixtyOneFC_709874603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1310025757004245097) ^ 655012878502122548 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1310025757004245097) ^ 45173301965663624 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1310025757004245097) ^ 31951847731810856 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1310025757004245097) ^ 10000196618353016 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1310025757004245097) ^ 884554866309416 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1310025757004245097) ^ 1845432632 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_2177812997739182333 : Nat.Prime 2177812997739182333 := by
  apply lucas_primality 2177812997739182333 (2 : ZMod 2177812997739182333)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2999, 1), (5806357, 1), (31266581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2999, 1), (5806357, 1), (31266581, 1)] : List FactorBlock).map factorBlockValue).prod) = 2177812997739182333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_2999
      · exact prime_oneHundredSixtyOneFC_5806357
      · exact prime_oneHundredSixtyOneFC_31266581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2177812997739182333) ^ 1088906498869591166 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2177812997739182333) ^ 726179725821668 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2177812997739182333) ^ 375073905676 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2177812997739182333) ^ 69653058572 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3648881479921507607 : Nat.Prime 3648881479921507607 := by
  apply lucas_primality 3648881479921507607 (5 : ZMod 3648881479921507607)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (53, 1), (557, 1), (8828779222349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (53, 1), (557, 1), (8828779222349, 1)] : List FactorBlock).map factorBlockValue).prod) = 3648881479921507607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_53
      · exact prime_oneHundredSixtyOneFC_557
      · exact prime_oneHundredSixtyOneFC_8828779222349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3648881479921507607) ^ 1824440739960753803 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3648881479921507607) ^ 521268782845929658 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3648881479921507607) ^ 68846820375877502 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3648881479921507607) ^ 6550954182982958 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3648881479921507607) ^ 413294 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_4984206892581708689 : Nat.Prime 4984206892581708689 := by
  apply lucas_primality 4984206892581708689 (3 : ZMod 4984206892581708689)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (67, 1), (45247, 1), (7904385889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (67, 1), (45247, 1), (7904385889, 1)] : List FactorBlock).map factorBlockValue).prod) = 4984206892581708689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_67
      · exact prime_oneHundredSixtyOneFC_45247
      · exact prime_oneHundredSixtyOneFC_7904385889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4984206892581708689) ^ 2492103446290854344 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4984206892581708689) ^ 383400530198592976 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4984206892581708689) ^ 74391147650473264 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4984206892581708689) ^ 110155521749104 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4984206892581708689) ^ 630562192 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_6822850619312808043 : Nat.Prime 6822850619312808043 := by
  apply lucas_primality 6822850619312808043 (13 : ZMod 6822850619312808043)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (9387527, 1), (1132086563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (9387527, 1), (1132086563, 1)] : List FactorBlock).map factorBlockValue).prod) = 6822850619312808043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_107
      · exact prime_oneHundredSixtyOneFC_9387527
      · exact prime_oneHundredSixtyOneFC_1132086563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 6822850619312808043) ^ 3411425309656404021 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 6822850619312808043) ^ 2274283539770936014 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 6822850619312808043) ^ 63764959058998206 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 6822850619312808043) ^ 726799573446 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (13 : ZMod 6822850619312808043) ^ 6026792334 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_8460299772588931549 : Nat.Prime 8460299772588931549 := by
  apply lucas_primality 8460299772588931549 (2 : ZMod 8460299772588931549)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (21569, 1), (22907, 1), (1426941863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (21569, 1), (22907, 1), (1426941863, 1)] : List FactorBlock).map factorBlockValue).prod) = 8460299772588931549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_21569
      · exact prime_oneHundredSixtyOneFC_22907
      · exact prime_oneHundredSixtyOneFC_1426941863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8460299772588931549) ^ 4230149886294465774 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8460299772588931549) ^ 2820099924196310516 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8460299772588931549) ^ 392243487068892 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8460299772588931549) ^ 369332508516564 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8460299772588931549) ^ 5928972996 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_10333938268729952771 : Nat.Prime 10333938268729952771 := by
  apply lucas_primality 10333938268729952771 (2 : ZMod 10333938268729952771)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (544139237, 1), (1899134921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (544139237, 1), (1899134921, 1)] : List FactorBlock).map factorBlockValue).prod) = 10333938268729952771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_544139237
      · exact prime_oneHundredSixtyOneFC_1899134921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10333938268729952771) ^ 5166969134364976385 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10333938268729952771) ^ 2066787653745990554 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10333938268729952771) ^ 18991349210 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10333938268729952771) ^ 5441392370 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_15602017149911940271 : Nat.Prime 15602017149911940271 := by
  apply lucas_primality 15602017149911940271 (3 : ZMod 15602017149911940271)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (61, 1), (13416959, 1), (33444289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (61, 1), (13416959, 1), (33444289, 1)] : List FactorBlock).map factorBlockValue).prod) = 15602017149911940271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_61
      · exact prime_oneHundredSixtyOneFC_13416959
      · exact prime_oneHundredSixtyOneFC_33444289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15602017149911940271) ^ 7801008574955970135 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 5200672383303980090 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 3120403429982388054 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 821158797363786330 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 255770772949376070 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 1162857928530 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 15602017149911940271) ^ 466507664430 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_16376048099917873357 : Nat.Prime 16376048099917873357 := by
  apply lucas_primality 16376048099917873357 (2 : ZMod 16376048099917873357)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (11278270041265753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (11278270041265753, 1)] : List FactorBlock).map factorBlockValue).prod) = 16376048099917873357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_11278270041265753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16376048099917873357) ^ 8188024049958936678 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 16376048099917873357) ^ 5458682699972624452 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 16376048099917873357) ^ 1488731645447079396 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 16376048099917873357) ^ 1452 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_17660765089967180327 : Nat.Prime 17660765089967180327 := by
  apply lucas_primality 17660765089967180327 (5 : ZMod 17660765089967180327)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2797, 1), (10211, 1), (309185255989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2797, 1), (10211, 1), (309185255989, 1)] : List FactorBlock).map factorBlockValue).prod) = 17660765089967180327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_2797
      · exact prime_oneHundredSixtyOneFC_10211
      · exact prime_oneHundredSixtyOneFC_309185255989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17660765089967180327) ^ 8830382544983590163 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 17660765089967180327) ^ 6314181297807358 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 17660765089967180327) ^ 1729582322002466 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 17660765089967180327) ^ 57120334 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_20496570876232764353 : Nat.Prime 20496570876232764353 := by
  apply lucas_primality 20496570876232764353 (5 : ZMod 20496570876232764353)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (41, 1), (600861013022771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (41, 1), (600861013022771, 1)] : List FactorBlock).map factorBlockValue).prod) = 20496570876232764353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_600861013022771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20496570876232764353) ^ 10248285438116382176 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 20496570876232764353) ^ 1576659298171751104 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 20496570876232764353) ^ 499916362834945472 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 20496570876232764353) ^ 34112 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_20667876537459905543 : Nat.Prime 20667876537459905543 := by
  apply lucas_primality 20667876537459905543 (5 : ZMod 20667876537459905543)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10333938268729952771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10333938268729952771, 1)] : List FactorBlock).map factorBlockValue).prod) = 20667876537459905543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_10333938268729952771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 20667876537459905543) ^ 10333938268729952771 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 20667876537459905543) ^ 2 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_23566059473170278539 : Nat.Prime 23566059473170278539 := by
  apply lucas_primality 23566059473170278539 (2 : ZMod 23566059473170278539)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (418373, 1), (908514013663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (418373, 1), (908514013663, 1)] : List FactorBlock).map factorBlockValue).prod) = 23566059473170278539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_418373
      · exact prime_oneHundredSixtyOneFC_908514013663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23566059473170278539) ^ 11783029736585139269 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 23566059473170278539) ^ 760195466876460598 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 23566059473170278539) ^ 56327868847106 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 23566059473170278539) ^ 25939126 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_26028262465358293799 : Nat.Prime 26028262465358293799 := by
  apply lucas_primality 26028262465358293799 (17 : ZMod 26028262465358293799)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (859, 1), (309190355008889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (859, 1), (309190355008889, 1)] : List FactorBlock).map factorBlockValue).prod) = 26028262465358293799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_859
      · exact prime_oneHundredSixtyOneFC_309190355008889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 26028262465358293799) ^ 13014131232679146899 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (17 : ZMod 26028262465358293799) ^ 3718323209336899114 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (17 : ZMod 26028262465358293799) ^ 30300654790871122 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (17 : ZMod 26028262465358293799) ^ 84182 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_30888966135739856369 : Nat.Prime 30888966135739856369 := by
  apply lucas_primality 30888966135739856369 (3 : ZMod 30888966135739856369)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (157, 1), (571, 1), (2099, 1), (1465673213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (157, 1), (571, 1), (2099, 1), (1465673213, 1)] : List FactorBlock).map factorBlockValue).prod) = 30888966135739856369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_157
      · exact prime_oneHundredSixtyOneFC_571
      · exact prime_oneHundredSixtyOneFC_2099
      · exact prime_oneHundredSixtyOneFC_1465673213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30888966135739856369) ^ 15444483067869928184 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 30888966135739856369) ^ 4412709447962836624 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 30888966135739856369) ^ 196745007234011824 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 30888966135739856369) ^ 54096262934745808 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 30888966135739856369) ^ 14716039130890832 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 30888966135739856369) ^ 21074933936 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_40518133960668803759 : Nat.Prime 40518133960668803759 := by
  apply lucas_primality 40518133960668803759 (11 : ZMod 40518133960668803759)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (740143, 1), (40792590343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (740143, 1), (40792590343, 1)] : List FactorBlock).map factorBlockValue).prod) = 40518133960668803759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_61
      · exact prime_oneHundredSixtyOneFC_740143
      · exact prime_oneHundredSixtyOneFC_40792590343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 40518133960668803759) ^ 20259066980334401879 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 40518133960668803759) ^ 3683466723697163978 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 40518133960668803759) ^ 664231704273259078 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 40518133960668803759) ^ 54743656240306 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 40518133960668803759) ^ 993271906 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_47132118946340557079 : Nat.Prime 47132118946340557079 := by
  apply lucas_primality 47132118946340557079 (11 : ZMod 47132118946340557079)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23566059473170278539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23566059473170278539, 1)] : List FactorBlock).map factorBlockValue).prod) = 47132118946340557079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_23566059473170278539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 47132118946340557079) ^ 23566059473170278539 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 47132118946340557079) ^ 2 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_50205693148235096401 : Nat.Prime 50205693148235096401 := by
  apply lucas_primality 50205693148235096401 (11 : ZMod 50205693148235096401)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (4184711, 1), (3332613859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (4184711, 1), (3332613859, 1)] : List FactorBlock).map factorBlockValue).prod) = 50205693148235096401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_4184711
      · exact prime_oneHundredSixtyOneFC_3332613859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 50205693148235096401) ^ 25102846574117548200 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 50205693148235096401) ^ 16735231049411698800 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 50205693148235096401) ^ 10041138629647019280 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 50205693148235096401) ^ 11997409892400 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (11 : ZMod 50205693148235096401) ^ 15064959600 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_192087739292377947377 : Nat.Prime 192087739292377947377 := by
  apply lucas_primality 192087739292377947377 (3 : ZMod 192087739292377947377)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (137, 1), (1246181, 1), (70319855563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (137, 1), (1246181, 1), (70319855563, 1)] : List FactorBlock).map factorBlockValue).prod) = 192087739292377947377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_137
      · exact prime_oneHundredSixtyOneFC_1246181
      · exact prime_oneHundredSixtyOneFC_70319855563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 192087739292377947377) ^ 96043869646188973688 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 192087739292377947377) ^ 1402100286805678448 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 192087739292377947377) ^ 154141123394096 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 192087739292377947377) ^ 2731628752 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_237411658455564283589 : Nat.Prime 237411658455564283589 := by
  apply lucas_primality 237411658455564283589 (2 : ZMod 237411658455564283589)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) = 237411658455564283589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_73
      · exact prime_oneHundredSixtyOneFC_79
      · exact prime_oneHundredSixtyOneFC_605401060944023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237411658455564283589) ^ 118705829227782141794 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 13965391673856722564 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3252214499391291556 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3005210866526130172 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 392156 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_288093312099915688409 : Nat.Prime 288093312099915688409 := by
  apply lucas_primality 288093312099915688409 (3 : ZMod 288093312099915688409)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 3), (104990274088890557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 3), (104990274088890557, 1)] : List FactorBlock).map factorBlockValue).prod) = 288093312099915688409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_104990274088890557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 288093312099915688409) ^ 144046656049957844204 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 288093312099915688409) ^ 41156187442845098344 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 288093312099915688409) ^ 2744 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_307956647081812084079 : Nat.Prime 307956647081812084079 := by
  apply lucas_primality 307956647081812084079 (22 : ZMod 307956647081812084079)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (41, 1), (5897, 1), (21960721505683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (41, 1), (5897, 1), (21960721505683, 1)] : List FactorBlock).map factorBlockValue).prod) = 307956647081812084079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_29
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_5897
      · exact prime_oneHundredSixtyOneFC_21960721505683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 307956647081812084079) ^ 153978323540906042039 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (22 : ZMod 307956647081812084079) ^ 10619194726959037382 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (22 : ZMod 307956647081812084079) ^ 7511137733702733758 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (22 : ZMod 307956647081812084079) ^ 52222595740514174 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (22 : ZMod 307956647081812084079) ^ 14023066 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_463720863845408091553 : Nat.Prime 463720863845408091553 := by
  apply lucas_primality 463720863845408091553 (10 : ZMod 463720863845408091553)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (7, 1), (20663, 1), (3710662694423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (7, 1), (20663, 1), (3710662694423, 1)] : List FactorBlock).map factorBlockValue).prod) = 463720863845408091553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_20663
      · exact prime_oneHundredSixtyOneFC_3710662694423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 463720863845408091553) ^ 231860431922704045776 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 463720863845408091553) ^ 154573621281802697184 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 463720863845408091553) ^ 66245837692201155936 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 463720863845408091553) ^ 22442087975870304 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (10 : ZMod 463720863845408091553) ^ 124969824 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_606482290201371401291 : Nat.Prime 606482290201371401291 := by
  apply lucas_primality 606482290201371401291 (2 : ZMod 606482290201371401291)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (41, 1), (593, 1), (8431, 1), (26897245013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (41, 1), (593, 1), (8431, 1), (26897245013, 1)] : List FactorBlock).map factorBlockValue).prod) = 606482290201371401291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_593
      · exact prime_oneHundredSixtyOneFC_8431
      · exact prime_oneHundredSixtyOneFC_26897245013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 606482290201371401291) ^ 303241145100685700645 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 606482290201371401291) ^ 121296458040274280258 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 606482290201371401291) ^ 55134753654670127390 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 606482290201371401291) ^ 14792250980521253690 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 606482290201371401291) ^ 1022735733897759530 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 606482290201371401291) ^ 71934798980117590 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 606482290201371401291) ^ 22548119330 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_607851951249969725009 : Nat.Prime 607851951249969725009 := by
  apply lucas_primality 607851951249969725009 (3 : ZMod 607851951249969725009)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (1310025757004245097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (1310025757004245097, 1)] : List FactorBlock).map factorBlockValue).prod) = 607851951249969725009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_29
      · exact prime_oneHundredSixtyOneFC_1310025757004245097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 607851951249969725009) ^ 303925975624984862504 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 607851951249969725009) ^ 20960412112067921552 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 607851951249969725009) ^ 464 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1701761626348089757879 : Nat.Prime 1701761626348089757879 := by
  apply lucas_primality 1701761626348089757879 (7 : ZMod 1701761626348089757879)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (40518133960668803759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (40518133960668803759, 1)] : List FactorBlock).map factorBlockValue).prod) = 1701761626348089757879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_40518133960668803759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1701761626348089757879) ^ 850880813174044878939 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1701761626348089757879) ^ 567253875449363252626 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1701761626348089757879) ^ 243108803764012822554 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1701761626348089757879) ^ 42 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_2596578010414202461219 : Nat.Prime 2596578010414202461219 := by
  apply lucas_primality 2596578010414202461219 (2 : ZMod 2596578010414202461219)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (283, 1), (5743, 1), (25873, 1), (71968433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (283, 1), (5743, 1), (25873, 1), (71968433, 1)] : List FactorBlock).map factorBlockValue).prod) = 2596578010414202461219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_283
      · exact prime_oneHundredSixtyOneFC_5743
      · exact prime_oneHundredSixtyOneFC_25873
      · exact prime_oneHundredSixtyOneFC_71968433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2596578010414202461219) ^ 1298289005207101230609 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2596578010414202461219) ^ 865526003471400820406 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2596578010414202461219) ^ 236052546401291132838 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2596578010414202461219) ^ 199736770031861727786 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2596578010414202461219) ^ 9175187315951245446 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2596578010414202461219) ^ 452129202579523326 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2596578010414202461219) ^ 100358598168523266 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2596578010414202461219) ^ 36079401790146 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_2994228031908734379569 : Nat.Prime 2994228031908734379569 := by
  apply lucas_primality 2994228031908734379569 (3 : ZMod 2994228031908734379569)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (48125003, 1), (3888607591241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (48125003, 1), (3888607591241, 1)] : List FactorBlock).map factorBlockValue).prod) = 2994228031908734379569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_48125003
      · exact prime_oneHundredSixtyOneFC_3888607591241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2994228031908734379569) ^ 1497114015954367189784 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2994228031908734379569) ^ 62217721459856 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2994228031908734379569) ^ 770000048 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_21500316536914473447941 : Nat.Prime 21500316536914473447941 := by
  apply lucas_primality 21500316536914473447941 (2 : ZMod 21500316536914473447941)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (59, 1), (281, 1), (707827, 1), (91607156309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (59, 1), (281, 1), (707827, 1), (91607156309, 1)] : List FactorBlock).map factorBlockValue).prod) = 21500316536914473447941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_59
      · exact prime_oneHundredSixtyOneFC_281
      · exact prime_oneHundredSixtyOneFC_707827
      · exact prime_oneHundredSixtyOneFC_91607156309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21500316536914473447941) ^ 10750158268457236723970 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 4300063307382894689588 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 364412144693465651660 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 76513581981902040740 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 30375100888938220 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21500316536914473447941) ^ 234701276660 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_26637343357582713807497 : Nat.Prime 26637343357582713807497 := by
  apply lucas_primality 26637343357582713807497 (3 : ZMod 26637343357582713807497)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1307, 1), (80221, 1), (260921, 1), (121710551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1307, 1), (80221, 1), (260921, 1), (121710551, 1)] : List FactorBlock).map factorBlockValue).prod) = 26637343357582713807497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_1307
      · exact prime_oneHundredSixtyOneFC_80221
      · exact prime_oneHundredSixtyOneFC_260921
      · exact prime_oneHundredSixtyOneFC_121710551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26637343357582713807497) ^ 13318671678791356903748 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 26637343357582713807497) ^ 20380522844363208728 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 26637343357582713807497) ^ 332049505211636776 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 26637343357582713807497) ^ 102089687520677576 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 26637343357582713807497) ^ 218858128064696 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_174403926267890422538081 : Nat.Prime 174403926267890422538081 := by
  apply lucas_primality 174403926267890422538081 (3 : ZMod 174403926267890422538081)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (37, 1), (1913, 1), (15527, 1), (991818096349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (37, 1), (1913, 1), (15527, 1), (991818096349, 1)] : List FactorBlock).map factorBlockValue).prod) = 174403926267890422538081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_37
      · exact prime_oneHundredSixtyOneFC_1913
      · exact prime_oneHundredSixtyOneFC_15527
      · exact prime_oneHundredSixtyOneFC_991818096349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 174403926267890422538081) ^ 87201963133945211269040 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 174403926267890422538081) ^ 34880785253578084507616 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 174403926267890422538081) ^ 4713619628861903311840 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 174403926267890422538081) ^ 91167760725504664160 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 174403926267890422538081) ^ 11232300268428571040 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 174403926267890422538081) ^ 175842653920 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_226337631115860832066153 : Nat.Prime 226337631115860832066153 := by
  apply lucas_primality 226337631115860832066153 (5 : ZMod 226337631115860832066153)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (41, 1), (955039, 1), (6509368184021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (41, 1), (955039, 1), (6509368184021, 1)] : List FactorBlock).map factorBlockValue).prod) = 226337631115860832066153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_37
      · exact prime_oneHundredSixtyOneFC_41
      · exact prime_oneHundredSixtyOneFC_955039
      · exact prime_oneHundredSixtyOneFC_6509368184021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 226337631115860832066153) ^ 113168815557930416033076 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 226337631115860832066153) ^ 75445877038620277355384 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 226337631115860832066153) ^ 6117233273401644109896 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 226337631115860832066153) ^ 5520430027216117855272 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 226337631115860832066153) ^ 236993076843836568 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 226337631115860832066153) ^ 34771059912 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_273342765725421349344203 : Nat.Prime 273342765725421349344203 := by
  apply lucas_primality 273342765725421349344203 (2 : ZMod 273342765725421349344203)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5395279, 1), (25331661784814219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5395279, 1), (25331661784814219, 1)] : List FactorBlock).map factorBlockValue).prod) = 273342765725421349344203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5395279
      · exact prime_oneHundredSixtyOneFC_25331661784814219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 273342765725421349344203) ^ 136671382862710674672101 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273342765725421349344203) ^ 50663323569628438 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273342765725421349344203) ^ 10790558 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_495799769064908666838569 : Nat.Prime 495799769064908666838569 := by
  apply lucas_primality 495799769064908666838569 (3 : ZMod 495799769064908666838569)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (19, 1), (557, 1), (4127, 1), (11727020864261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (19, 1), (557, 1), (4127, 1), (11727020864261, 1)] : List FactorBlock).map factorBlockValue).prod) = 495799769064908666838569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_557
      · exact prime_oneHundredSixtyOneFC_4127
      · exact prime_oneHundredSixtyOneFC_11727020864261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 495799769064908666838569) ^ 247899884532454333419284 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 45072706278628060621688 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 26094724687626771938872 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 890125258644360263624 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 120135635828666989784 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 495799769064908666838569) ^ 42278407688 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_577767631228367397774251 : Nat.Prime 577767631228367397774251 := by
  apply lucas_primality 577767631228367397774251 (2 : ZMod 577767631228367397774251)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (19, 1), (3251, 1), (107101, 1), (49905804659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (19, 1), (3251, 1), (107101, 1), (49905804659, 1)] : List FactorBlock).map factorBlockValue).prod) = 577767631228367397774251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_3251
      · exact prime_oneHundredSixtyOneFC_107101
      · exact prime_oneHundredSixtyOneFC_49905804659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 577767631228367397774251) ^ 288883815614183698887125 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 577767631228367397774251) ^ 115553526245673479554850 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 577767631228367397774251) ^ 82538233032623913967750 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 577767631228367397774251) ^ 30408822696229863040750 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 577767631228367397774251) ^ 177719972694053336750 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 577767631228367397774251) ^ 5394605383968099250 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 577767631228367397774251) ^ 11577162920750 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_4138473895302744071603453 : Nat.Prime 4138473895302744071603453 := by
  apply lucas_primality 4138473895302744071603453 (5 : ZMod 4138473895302744071603453)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (541, 1), (1063, 1), (114769, 1), (203579656097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (541, 1), (1063, 1), (114769, 1), (203579656097, 1)] : List FactorBlock).map factorBlockValue).prod) = 4138473895302744071603453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_541
      · exact prime_oneHundredSixtyOneFC_1063
      · exact prime_oneHundredSixtyOneFC_114769
      · exact prime_oneHundredSixtyOneFC_203579656097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4138473895302744071603453) ^ 2069236947651372035801726 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4138473895302744071603453) ^ 591210556471820581657636 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4138473895302744071603453) ^ 376224899572976733782132 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4138473895302744071603453) ^ 7649674482999526934572 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4138473895302744071603453) ^ 3893202159268809098404 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4138473895302744071603453) ^ 36059161405107163708 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4138473895302744071603453) ^ 20328523854716 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_4613081487580689516488033 : Nat.Prime 4613081487580689516488033 := by
  apply lucas_primality 4613081487580689516488033 (5 : ZMod 4613081487580689516488033)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613081487580689516488033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_97
      · exact prime_oneHundredSixtyOneFC_719
      · exact prime_oneHundredSixtyOneFC_17207
      · exact prime_oneHundredSixtyOneFC_17160791887493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4613081487580689516488033) ^ 2306540743790344758244016 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 659011641082955645212576 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 47557541109079273365856 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 6415968689263824084128 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268093304328511042976 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268815187424 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_11480396160467696672456527 : Nat.Prime 11480396160467696672456527 := by
  apply lucas_primality 11480396160467696672456527 (3 : ZMod 11480396160467696672456527)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (273342765725421349344203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (273342765725421349344203, 1)] : List FactorBlock).map factorBlockValue).prod) = 11480396160467696672456527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_273342765725421349344203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11480396160467696672456527) ^ 5740198080233848336228263 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11480396160467696672456527) ^ 3826798720155898890818842 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11480396160467696672456527) ^ 1640056594352528096065218 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11480396160467696672456527) ^ 42 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_30770282628605627356826579 : Nat.Prime 30770282628605627356826579 := by
  apply lucas_primality 30770282628605627356826579 (2 : ZMod 30770282628605627356826579)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7591387, 1), (34897321, 1), (58074873107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7591387, 1), (34897321, 1), (58074873107, 1)] : List FactorBlock).map factorBlockValue).prod) = 30770282628605627356826579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_7591387
      · exact prime_oneHundredSixtyOneFC_34897321
      · exact prime_oneHundredSixtyOneFC_58074873107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30770282628605627356826579) ^ 15385141314302813678413289 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30770282628605627356826579) ^ 4053314977698492694 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30770282628605627356826579) ^ 881737673462258818 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30770282628605627356826579) ^ 529838137948454 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_38406975048538016712939713 : Nat.Prime 38406975048538016712939713 := by
  apply lucas_primality 38406975048538016712939713 (3 : ZMod 38406975048538016712939713)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (411211963949, 1), (1459366549967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (411211963949, 1), (1459366549967, 1)] : List FactorBlock).map factorBlockValue).prod) = 38406975048538016712939713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_411211963949
      · exact prime_oneHundredSixtyOneFC_1459366549967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38406975048538016712939713) ^ 19203487524269008356469856 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 38406975048538016712939713) ^ 93399459197888 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 38406975048538016712939713) ^ 26317565692736 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_40542059284463133296981729 : Nat.Prime 40542059284463133296981729 := by
  apply lucas_primality 40542059284463133296981729 (3 : ZMod 40542059284463133296981729)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (24391, 1), (33317, 1), (82055317465903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (24391, 1), (33317, 1), (82055317465903, 1)] : List FactorBlock).map factorBlockValue).prod) = 40542059284463133296981729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_19
      · exact prime_oneHundredSixtyOneFC_24391
      · exact prime_oneHundredSixtyOneFC_33317
      · exact prime_oneHundredSixtyOneFC_82055317465903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40542059284463133296981729) ^ 20271029642231566648490864 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 40542059284463133296981729) ^ 2133792593919112278788512 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 40542059284463133296981729) ^ 1662172903302986072608 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 40542059284463133296981729) ^ 1216858038972990764384 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 40542059284463133296981729) ^ 494082047776 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_66554184734459584206059167 : Nat.Prime 66554184734459584206059167 := by
  apply lucas_primality 66554184734459584206059167 (3 : ZMod 66554184734459584206059167)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (10936069, 1), (12201611, 1), (4889863987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (10936069, 1), (12201611, 1), (4889863987, 1)] : List FactorBlock).map factorBlockValue).prod) = 66554184734459584206059167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_10936069
      · exact prime_oneHundredSixtyOneFC_12201611
      · exact prime_oneHundredSixtyOneFC_4889863987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66554184734459584206059167) ^ 33277092367229792103029583 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 66554184734459584206059167) ^ 22184728244819861402019722 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 66554184734459584206059167) ^ 3914952043203504953297598 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 66554184734459584206059167) ^ 6085750257652871814 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 66554184734459584206059167) ^ 5454540776169604506 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 66554184734459584206059167) ^ 13610641300330218 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_96328425273559924508769847 : Nat.Prime 96328425273559924508769847 := by
  apply lucas_primality 96328425273559924508769847 (5 : ZMod 96328425273559924508769847)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (61, 1), (4203967, 1), (17741279, 1), (504116731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (61, 1), (4203967, 1), (17741279, 1), (504116731, 1)] : List FactorBlock).map factorBlockValue).prod) = 96328425273559924508769847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_61
      · exact prime_oneHundredSixtyOneFC_4203967
      · exact prime_oneHundredSixtyOneFC_17741279
      · exact prime_oneHundredSixtyOneFC_504116731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 96328425273559924508769847) ^ 48164212636779962254384923 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 96328425273559924508769847) ^ 32109475091186641502923282 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 96328425273559924508769847) ^ 13761203610508560644109978 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 96328425273559924508769847) ^ 1579154512681310237848686 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 96328425273559924508769847) ^ 22913696818638187338 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 96328425273559924508769847) ^ 5429621239458548874 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 96328425273559924508769847) ^ 191083571224617666 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_109898942459904394243261673 : Nat.Prime 109898942459904394243261673 := by
  apply lucas_primality 109898942459904394243261673 (5 : ZMod 109898942459904394243261673)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (13, 1), (44111, 1), (2177812997739182333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (13, 1), (44111, 1), (2177812997739182333, 1)] : List FactorBlock).map factorBlockValue).prod) = 109898942459904394243261673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_11
      · exact prime_oneHundredSixtyOneFC_13
      · exact prime_oneHundredSixtyOneFC_44111
      · exact prime_oneHundredSixtyOneFC_2177812997739182333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 109898942459904394243261673) ^ 54949471229952197121630836 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 109898942459904394243261673) ^ 9990812950900399476660152 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 109898942459904394243261673) ^ 8453764804608030326404744 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 109898942459904394243261673) ^ 2491418069413624588952 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 109898942459904394243261673) ^ 50462984 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_504893815226934776735621267 : Nat.Prime 504893815226934776735621267 := by
  apply lucas_primality 504893815226934776735621267 (2 : ZMod 504893815226934776735621267)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (4138473895302744071603453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (4138473895302744071603453, 1)] : List FactorBlock).map factorBlockValue).prod) = 504893815226934776735621267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_61
      · exact prime_oneHundredSixtyOneFC_4138473895302744071603453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 504893815226934776735621267) ^ 252446907613467388367810633 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 504893815226934776735621267) ^ 8276947790605488143206906 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 504893815226934776735621267) ^ 122 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_638741504498504734326608113 : Nat.Prime 638741504498504734326608113 := by
  apply lucas_primality 638741504498504734326608113 (5 : ZMod 638741504498504734326608113)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (6173, 1), (307956647081812084079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (6173, 1), (307956647081812084079, 1)] : List FactorBlock).map factorBlockValue).prod) = 638741504498504734326608113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_6173
      · exact prime_oneHundredSixtyOneFC_307956647081812084079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 638741504498504734326608113) ^ 319370752249252367163304056 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 638741504498504734326608113) ^ 212913834832834911442202704 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 638741504498504734326608113) ^ 91248786356929247760944016 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 638741504498504734326608113) ^ 103473433419488860250544 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 638741504498504734326608113) ^ 2074128 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_976128042772073901688867783 : Nat.Prime 976128042772073901688867783 := by
  apply lucas_primality 976128042772073901688867783 (3 : ZMod 976128042772073901688867783)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (347, 1), (563, 1), (1637, 1), (169569498386672207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (347, 1), (563, 1), (1637, 1), (169569498386672207, 1)] : List FactorBlock).map factorBlockValue).prod) = 976128042772073901688867783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_347
      · exact prime_oneHundredSixtyOneFC_563
      · exact prime_oneHundredSixtyOneFC_1637
      · exact prime_oneHundredSixtyOneFC_169569498386672207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 976128042772073901688867783) ^ 488064021386036950844433891 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 976128042772073901688867783) ^ 325376014257357967229622594 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 976128042772073901688867783) ^ 2813049114616927670573106 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 976128042772073901688867783) ^ 1733797589293204088257314 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 976128042772073901688867783) ^ 596290801937736042571086 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 976128042772073901688867783) ^ 5756507226 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_1303732659866811033077597381 : Nat.Prime 1303732659866811033077597381 := by
  apply lucas_primality 1303732659866811033077597381 (3 : ZMod 1303732659866811033077597381)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (8269, 1), (463720863845408091553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (8269, 1), (463720863845408091553, 1)] : List FactorBlock).map factorBlockValue).prod) = 1303732659866811033077597381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_5
      · exact prime_oneHundredSixtyOneFC_17
      · exact prime_oneHundredSixtyOneFC_8269
      · exact prime_oneHundredSixtyOneFC_463720863845408091553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1303732659866811033077597381) ^ 651866329933405516538798690 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1303732659866811033077597381) ^ 260746531973362206615519476 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1303732659866811033077597381) ^ 76690156462753590181035140 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1303732659866811033077597381) ^ 157665093707438751128020 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1303732659866811033077597381) ^ 2811460 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3226185904077193403886935893 : Nat.Prime 3226185904077193403886935893 := by
  apply lucas_primality 3226185904077193403886935893 (5 : ZMod 3226185904077193403886935893)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (38406975048538016712939713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (38406975048538016712939713, 1)] : List FactorBlock).map factorBlockValue).prod) = 3226185904077193403886935893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_7
      · exact prime_oneHundredSixtyOneFC_38406975048538016712939713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3226185904077193403886935893) ^ 1613092952038596701943467946 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3226185904077193403886935893) ^ 1075395301359064467962311964 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3226185904077193403886935893) ^ 460883700582456200555276556 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3226185904077193403886935893) ^ 84 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_3732254281187341388810376817 : Nat.Prime 3732254281187341388810376817 := by
  apply lucas_primality 3732254281187341388810376817 (5 : ZMod 3732254281187341388810376817)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (2531, 1), (15121, 1), (65538369885629057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (2531, 1), (15121, 1), (65538369885629057, 1)] : List FactorBlock).map factorBlockValue).prod) = 3732254281187341388810376817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_3
      · exact prime_oneHundredSixtyOneFC_31
      · exact prime_oneHundredSixtyOneFC_2531
      · exact prime_oneHundredSixtyOneFC_15121
      · exact prime_oneHundredSixtyOneFC_65538369885629057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3732254281187341388810376817) ^ 1866127140593670694405188408 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3732254281187341388810376817) ^ 1244084760395780462936792272 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3732254281187341388810376817) ^ 120395299393140044800334736 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3732254281187341388810376817) ^ 1474616468268408292694736 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3732254281187341388810376817) ^ 246825889900624389181296 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3732254281187341388810376817) ^ 56947621488 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_7049813642242755956641822877 : Nat.Prime 7049813642242755956641822877 := by
  apply lucas_primality 7049813642242755956641822877 (2 : ZMod 7049813642242755956641822877)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6904748117809, 1), (255252382923991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6904748117809, 1), (255252382923991, 1)] : List FactorBlock).map factorBlockValue).prod) = 7049813642242755956641822877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_6904748117809
      · exact prime_oneHundredSixtyOneFC_255252382923991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7049813642242755956641822877) ^ 3524906821121377978320911438 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7049813642242755956641822877) ^ 1021009531695964 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7049813642242755956641822877) ^ 27618992471236 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyOneFC_27192138334364915832761316803 : Nat.Prime 27192138334364915832761316803 := by
  apply lucas_primality 27192138334364915832761316803 (2 : ZMod 27192138334364915832761316803)
  · rw [← oneHundredSixtyOneFCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10979, 1), (15149, 1), (63029, 1), (9642827, 1), (134499857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10979, 1), (15149, 1), (63029, 1), (9642827, 1), (134499857, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364915832761316803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyOneFC_2
      · exact prime_oneHundredSixtyOneFC_10979
      · exact prime_oneHundredSixtyOneFC_15149
      · exact prime_oneHundredSixtyOneFC_63029
      · exact prime_oneHundredSixtyOneFC_9642827
      · exact prime_oneHundredSixtyOneFC_134499857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27192138334364915832761316803) ^ 13596069167182457916380658401 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 2476740899386548486452438 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 1794979096598119732837898 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 431422652023115007897338 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 2819934271802752017926 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27192138334364915832761316803) ^ 202172247174693396386 ≠ 1
      rw [← oneHundredSixtyOneFCFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217600 : Nat.totient 190344968340554410829329217600 = 62423327186090473929689088000 := by
  rw [← show ((([(2, 6), (5, 2), (7, 1), (23, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_23, prime_oneHundredSixtyOneFC_171401, prime_oneHundredSixtyOneFC_714027719, prime_oneHundredSixtyOneFC_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217601 : Nat.totient 190344968340554410829329217601 = 118043833776992486028411863040 := by
  rw [← show ((([(3, 1), (29, 1), (47, 1), (67, 1), (1549, 1), (28019, 1), (32158261, 1), (497797697, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_29, prime_oneHundredSixtyOneFC_47, prime_oneHundredSixtyOneFC_67, prime_oneHundredSixtyOneFC_1549, prime_oneHundredSixtyOneFC_28019, prime_oneHundredSixtyOneFC_32158261, prime_oneHundredSixtyOneFC_497797697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217602 : Nat.totient 190344968340554410829329217602 = 94890368352464810292744057600 := by
  rw [← show ((([(2, 1), (379, 1), (3253, 1), (70381, 1), (365039, 1), (478991, 1), (6272867, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_379, prime_oneHundredSixtyOneFC_3253, prime_oneHundredSixtyOneFC_70381, prime_oneHundredSixtyOneFC_365039, prime_oneHundredSixtyOneFC_478991, prime_oneHundredSixtyOneFC_6272867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217603 : Nat.totient 190344968340554410829329217603 = 190088412697414433477013765120 := by
  rw [← show ((([(839, 1), (6871, 1), (94397, 1), (206774753, 1), (1691623807, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_839, prime_oneHundredSixtyOneFC_6871, prime_oneHundredSixtyOneFC_94397, prime_oneHundredSixtyOneFC_206774753, prime_oneHundredSixtyOneFC_1691623807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217604 : Nat.totient 190344968340554410829329217604 = 63441514289333745402359949216 := by
  rw [← show ((([(2, 2), (3, 1), (9319, 1), (173863364119, 1), (9790001640347, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_9319, prime_oneHundredSixtyOneFC_173863364119, prime_oneHundredSixtyOneFC_9790001640347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217605 : Nat.totient 190344968340554410829329217605 = 151622421650314739000765128704 := by
  rw [← show ((([(5, 1), (233, 1), (25493933, 1), (71608973, 1), (89497558993, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_233, prime_oneHundredSixtyOneFC_25493933, prime_oneHundredSixtyOneFC_71608973, prime_oneHundredSixtyOneFC_89497558993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217606 : Nat.totient 190344968340554410829329217606 = 92959170584848236243010346400 := by
  rw [← show ((([(2, 1), (43, 1), (1262478147181, 1), (1753150017128941, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_43, prime_oneHundredSixtyOneFC_1262478147181, prime_oneHundredSixtyOneFC_1753150017128941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217607 : Nat.totient 190344968340554410829329217607 = 97607018113127173820461824000 := by
  rw [← show ((([(3, 2), (7, 1), (13, 1), (41, 1), (421, 1), (863, 1), (15602017149911940271, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_13, prime_oneHundredSixtyOneFC_41, prime_oneHundredSixtyOneFC_421, prime_oneHundredSixtyOneFC_863, prime_oneHundredSixtyOneFC_15602017149911940271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217608 : Nat.totient 190344968340554410829329217608 = 94444419658950405197834586880 := by
  rw [← show ((([(2, 3), (131, 1), (60659, 1), (2994228031908734379569, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_131, prime_oneHundredSixtyOneFC_60659, prime_oneHundredSixtyOneFC_2994228031908734379569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217609 : Nat.totient 190344968340554410829329217609 = 169331334824995019468579082240 := by
  rw [← show ((([(11, 1), (89, 1), (97, 1), (122399, 1), (16376048099917873357, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_11, prime_oneHundredSixtyOneFC_89, prime_oneHundredSixtyOneFC_97, prime_oneHundredSixtyOneFC_122399, prime_oneHundredSixtyOneFC_16376048099917873357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217610 : Nat.totient 190344968340554410829329217610 = 50536901077382609106321373440 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (229, 2), (487727, 1), (248068935643532141, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_229, prime_oneHundredSixtyOneFC_487727, prime_oneHundredSixtyOneFC_248068935643532141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217611 : Nat.totient 190344968340554410829329217611 = 190332868340279067848675561760 := by
  rw [← show ((([(15731, 1), (22017995773, 1), (549550093265597, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_15731, prime_oneHundredSixtyOneFC_22017995773, prime_oneHundredSixtyOneFC_549550093265597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217612 : Nat.totient 190344968340554410829329217612 = 95172484170236292072979084080 := by
  rw [← show ((([(2, 2), (2326461371621, 1), (20454344381390743, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_2326461371621, prime_oneHundredSixtyOneFC_20454344381390743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217613 : Nat.totient 190344968340554410829329217613 = 126896529463237144341438303024 := by
  rw [← show ((([(3, 1), (1110539, 1), (69292543, 1), (824517412163923, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_1110539, prime_oneHundredSixtyOneFC_69292543, prime_oneHundredSixtyOneFC_824517412163923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217614 : Nat.totient 190344968340554410829329217614 = 81562297204189241188291479552 := by
  rw [← show ((([(2, 1), (7, 1), (10979, 1), (15149, 1), (63029, 1), (9642827, 1), (134499857, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_10979, prime_oneHundredSixtyOneFC_15149, prime_oneHundredSixtyOneFC_63029, prime_oneHundredSixtyOneFC_9642827, prime_oneHundredSixtyOneFC_134499857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217615 : Nat.totient 190344968340554410829329217615 = 144261262736066593121700956832 := by
  rw [← show ((([(5, 1), (19, 1), (771643, 1), (2596578010414202461219, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_19, prime_oneHundredSixtyOneFC_771643, prime_oneHundredSixtyOneFC_2596578010414202461219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217616 : Nat.totient 190344968340554410829329217616 = 57763090627358968088100864000 := by
  rw [← show ((([(2, 4), (3, 2), (17, 1), (31, 1), (2531, 1), (15121, 1), (65538369885629057, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_17, prime_oneHundredSixtyOneFC_31, prime_oneHundredSixtyOneFC_2531, prime_oneHundredSixtyOneFC_15121, prime_oneHundredSixtyOneFC_65538369885629057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217617 : Nat.totient 190344968340554410829329217617 = 190344366181225950134334432000 := by
  rw [← show ((([(317351, 1), (80445121, 1), (7455929975633927, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_317351, prime_oneHundredSixtyOneFC_80445121, prime_oneHundredSixtyOneFC_7455929975633927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217618 : Nat.totient 190344968340554410829329217618 = 95172457532933847831947228416 := by
  rw [← show ((([(2, 1), (3572897, 1), (26637343357582713807497, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3572897, prime_oneHundredSixtyOneFC_26637343357582713807497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217619 : Nat.totient 190344968340554410829329217619 = 126060052020893997768689184000 := by
  rw [← show ((([(3, 1), (191, 1), (733, 1), (12133835171, 1), (37349493207721, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_191, prime_oneHundredSixtyOneFC_733, prime_oneHundredSixtyOneFC_12133835171, prime_oneHundredSixtyOneFC_37349493207721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217620 : Nat.totient 190344968340554410829329217620 = 63892017345081200837816799360 := by
  rw [← show ((([(2, 2), (5, 1), (11, 1), (13, 1), (66554184734459584206059167, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_11, prime_oneHundredSixtyOneFC_13, prime_oneHundredSixtyOneFC_66554184734459584206059167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217621 : Nat.totient 190344968340554410829329217621 = 163152830006189494996567900812 := by
  rw [← show ((([(7, 1), (27192138334364915832761316803, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_27192138334364915832761316803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217622 : Nat.totient 190344968340554410829329217622 = 63422240355920368493242302240 := by
  rw [← show ((([(2, 1), (3, 1), (2467, 1), (174467, 1), (754596511, 1), (97677135503, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_2467, prime_oneHundredSixtyOneFC_174467, prime_oneHundredSixtyOneFC_754596511, prime_oneHundredSixtyOneFC_97677135503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217623 : Nat.totient 190344968340554410829329217623 = 182069100150663342382743441024 := by
  rw [← show ((([(23, 1), (155440836073, 1), (53241274286720537, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_23, prime_oneHundredSixtyOneFC_155440836073, prime_oneHundredSixtyOneFC_53241274286720537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217624 : Nat.totient 190344968340554410829329217624 = 93499535554885104345385198080 := by
  rw [← show ((([(2, 3), (71, 1), (293, 1), (7639, 1), (23956067, 1), (6249904997477, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_71, prime_oneHundredSixtyOneFC_293, prime_oneHundredSixtyOneFC_7639, prime_oneHundredSixtyOneFC_23956067, prime_oneHundredSixtyOneFC_6249904997477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217625 : Nat.totient 190344968340554410829329217625 = 101516964865956028914803712000 := by
  rw [← show ((([(3, 4), (5, 3), (289171, 1), (195689519, 1), (332218693889, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_289171, prime_oneHundredSixtyOneFC_195689519, prime_oneHundredSixtyOneFC_332218693889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217626 : Nat.totient 190344968340554410829329217626 = 93868751510410394381587011360 := by
  rw [← show ((([(2, 1), (73, 1), (1303732659866811033077597381, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_73, prime_oneHundredSixtyOneFC_1303732659866811033077597381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217627 : Nat.totient 190344968340554410829329217627 = 190338569519725909757288253024 := by
  rw [← show ((([(31019, 1), (725317, 1), (8460299772588931549, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_31019, prime_oneHundredSixtyOneFC_725317, prime_oneHundredSixtyOneFC_8460299772588931549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217628 : Nat.totient 190344968340554410829329217628 = 53462509267564919264412079104 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (59, 1), (38406975048538016712939713, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_59, prime_oneHundredSixtyOneFC_38406975048538016712939713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217629 : Nat.totient 190344968340554410829329217629 = 183848681196779210726629709952 := by
  rw [← show ((([(37, 1), (137, 1), (104970939287, 1), (357725604662743, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_37, prime_oneHundredSixtyOneFC_137, prime_oneHundredSixtyOneFC_104970939287, prime_oneHundredSixtyOneFC_357725604662743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217630 : Nat.totient 190344968340554410829329217630 = 73415939575707035337460684800 := by
  rw [← show ((([(2, 1), (5, 1), (29, 1), (761, 1), (88272264991, 1), (9770897917097, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_29, prime_oneHundredSixtyOneFC_761, prime_oneHundredSixtyOneFC_88272264991, prime_oneHundredSixtyOneFC_9770897917097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217631 : Nat.totient 190344968340554410829329217631 = 115360586872256373536166621920 := by
  rw [← show ((([(3, 1), (11, 1), (142967124779, 1), (40345144749671933, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_11, prime_oneHundredSixtyOneFC_142967124779, prime_oneHundredSixtyOneFC_40345144749671933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217632 : Nat.totient 190344968340554410829329217632 = 93770762981711978957495500800 := by
  rw [← show ((([(2, 5), (113, 1), (367, 1), (599, 1), (727, 1), (5813, 1), (1081051, 1), (52413019, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_113, prime_oneHundredSixtyOneFC_367, prime_oneHundredSixtyOneFC_599, prime_oneHundredSixtyOneFC_727, prime_oneHundredSixtyOneFC_5813, prime_oneHundredSixtyOneFC_1081051, prime_oneHundredSixtyOneFC_52413019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217633 : Nat.totient 190344968340554410829329217633 = 165367125649138523624192194560 := by
  rw [← show ((([(13, 1), (17, 1), (403219, 1), (4291097, 1), (497782709415311, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_13, prime_oneHundredSixtyOneFC_17, prime_oneHundredSixtyOneFC_403219, prime_oneHundredSixtyOneFC_4291097, prime_oneHundredSixtyOneFC_497782709415311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217634 : Nat.totient 190344968340554410829329217634 = 60084492906540879923608974528 := by
  rw [← show ((([(2, 1), (3, 2), (19, 1), (2459, 1), (226337631115860832066153, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_19, prime_oneHundredSixtyOneFC_2459, prime_oneHundredSixtyOneFC_226337631115860832066153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217635 : Nat.totient 190344968340554410829329217635 = 130438969643748691341225177984 := by
  rw [← show ((([(5, 1), (7, 2), (1567, 1), (495799769064908666838569, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_1567, prime_oneHundredSixtyOneFC_495799769064908666838569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217636 : Nat.totient 190344968340554410829329217636 = 94952686285357396626178084608 := by
  rw [← show ((([(2, 2), (433, 1), (109898942459904394243261673, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_433, prime_oneHundredSixtyOneFC_109898942459904394243261673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217637 : Nat.totient 190344968340554410829329217637 = 126896645519376465460896167168 := by
  rw [← show ((([(3, 1), (3095557943, 1), (20496570876232764353, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_3095557943, prime_oneHundredSixtyOneFC_20496570876232764353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217638 : Nat.totient 190344968340554410829329217638 = 95172482468515579066518925080 := by
  rw [← show ((([(2, 1), (55925861, 1), (1701761626348089757879, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_55925861, prime_oneHundredSixtyOneFC_1701761626348089757879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217639 : Nat.totient 190344968340554410829329217639 = 190343976833736692196970831200 := by
  rw [← show ((([(194581, 1), (14336549, 1), (68233295411240431, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_194581, prime_oneHundredSixtyOneFC_14336549, prime_oneHundredSixtyOneFC_68233295411240431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217640 : Nat.totient 190344968340554410829329217640 = 50758649005161855690342907392 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (5505883, 1), (288093312099915688409, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_5505883, prime_oneHundredSixtyOneFC_288093312099915688409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217641 : Nat.totient 190344968340554410829329217641 = 190341291922541552988700476048 := by
  rw [← show ((([(52579, 1), (3579119, 1), (62319643, 1), (16230353687, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_52579, prime_oneHundredSixtyOneFC_3579119, prime_oneHundredSixtyOneFC_62319643, prime_oneHundredSixtyOneFC_16230353687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217642 : Nat.totient 190344968340554410829329217642 = 73884404155584721791079953600 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (269, 1), (260171, 1), (17660765089967180327, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_11, prime_oneHundredSixtyOneFC_269, prime_oneHundredSixtyOneFC_260171, prime_oneHundredSixtyOneFC_17660765089967180327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217643 : Nat.totient 190344968340554410829329217643 = 126895599136811999877016855680 := by
  rw [← show ((([(3, 2), (121267, 1), (174403926267890422538081, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_121267, prime_oneHundredSixtyOneFC_174403926267890422538081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217644 : Nat.totient 190344968340554410829329217644 = 94965505661455252994882322432 := by
  rw [← show ((([(2, 2), (857, 1), (1019, 1), (36277, 1), (5096737, 1), (294715389733, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_857, prime_oneHundredSixtyOneFC_1019, prime_oneHundredSixtyOneFC_36277, prime_oneHundredSixtyOneFC_5096737, prime_oneHundredSixtyOneFC_294715389733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217645 : Nat.totient 190344968340554410829329217645 = 148001846108092205331766809600 := by
  rw [← show ((([(5, 1), (79, 1), (101, 2), (197, 1), (1447, 1), (165716899991283989, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_79, prime_oneHundredSixtyOneFC_101, prime_oneHundredSixtyOneFC_197, prime_oneHundredSixtyOneFC_1447, prime_oneHundredSixtyOneFC_165716899991283989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217646 : Nat.totient 190344968340554410829329217646 = 56021261585179893488230660608 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (23, 2), (4613081487580689516488033, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_13, prime_oneHundredSixtyOneFC_23, prime_oneHundredSixtyOneFC_4613081487580689516488033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217647 : Nat.totient 190344968340554410829329217647 = 184178585212043086547622230400 := by
  rw [← show ((([(31, 1), (7331, 1), (168043, 1), (4984206892581708689, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_31, prime_oneHundredSixtyOneFC_7331, prime_oneHundredSixtyOneFC_168043, prime_oneHundredSixtyOneFC_4984206892581708689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217648 : Nat.totient 190344968340554410829329217648 = 89385881823889909013159884800 := by
  rw [← show ((([(2, 4), (41, 1), (47, 1), (61, 1), (6386664563, 1), (15846587816023, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_41, prime_oneHundredSixtyOneFC_47, prime_oneHundredSixtyOneFC_61, prime_oneHundredSixtyOneFC_6386664563, prime_oneHundredSixtyOneFC_15846587816023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217649 : Nat.totient 190344968340554410829329217649 = 106172282470548487832155883520 := by
  rw [← show ((([(3, 1), (7, 1), (43, 1), (1597, 1), (432499, 1), (305185311208195361, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_43, prime_oneHundredSixtyOneFC_1597, prime_oneHundredSixtyOneFC_432499, prime_oneHundredSixtyOneFC_305185311208195361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217650 : Nat.totient 190344968340554410829329217650 = 69966737099835976818652815360 := by
  rw [← show ((([(2, 1), (5, 2), (17, 1), (53, 1), (223, 1), (2777, 1), (6822850619312808043, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_17, prime_oneHundredSixtyOneFC_53, prime_oneHundredSixtyOneFC_223, prime_oneHundredSixtyOneFC_2777, prime_oneHundredSixtyOneFC_6822850619312808043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217651 : Nat.totient 190344968340554410829329217651 = 190344968340537897792540116832 := by
  rw [← show ((([(11535008805553, 1), (16501501780295267, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_11535008805553, prime_oneHundredSixtyOneFC_16501501780295267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217652 : Nat.totient 190344968340554410829329217652 = 63448322780175365953058901120 := by
  rw [← show ((([(2, 2), (3, 3), (6904748117809, 1), (255252382923991, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_6904748117809, prime_oneHundredSixtyOneFC_255252382923991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217653 : Nat.totient 190344968340554410829329217653 = 163623992118571480671197557920 := by
  rw [← show ((([(11, 2), (19, 1), (587, 1), (5419, 1), (26028262465358293799, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_11, prime_oneHundredSixtyOneFC_19, prime_oneHundredSixtyOneFC_587, prime_oneHundredSixtyOneFC_5419, prime_oneHundredSixtyOneFC_26028262465358293799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217654 : Nat.totient 190344968340554410829329217654 = 94679356559956965352579860480 := by
  rw [← show ((([(2, 1), (193, 1), (15964331, 1), (30888966135739856369, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_193, prime_oneHundredSixtyOneFC_15964331, prime_oneHundredSixtyOneFC_30888966135739856369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217655 : Nat.totient 190344968340554410829329217655 = 101192979974019980709266393088 := by
  rw [← show ((([(3, 1), (5, 1), (313, 1), (40542059284463133296981729, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_313, prime_oneHundredSixtyOneFC_40542059284463133296981729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217656 : Nat.totient 190344968340554410829329217656 = 80934081026653233608827070592 := by
  rw [← show ((([(2, 3), (7, 1), (127, 1), (2577668428667, 1), (10382993943589, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_127, prime_oneHundredSixtyOneFC_2577668428667, prime_oneHundredSixtyOneFC_10382993943589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217657 : Nat.totient 190344968340554410829329217657 = 190344967734072120627643965540 := by
  rw [← show ((([(313850827, 1), (606482290201371401291, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_313850827, prime_oneHundredSixtyOneFC_606482290201371401291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217658 : Nat.totient 190344968340554410829329217658 = 63446122432308562853244611328 := by
  rw [← show ((([(2, 1), (3, 1), (28837, 1), (588497713, 1), (1869370107385603, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_28837, prime_oneHundredSixtyOneFC_588497713, prime_oneHundredSixtyOneFC_1869370107385603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217659 : Nat.totient 190344968340554410829329217659 = 169644321916250084983168745376 := by
  rw [← show ((([(13, 1), (29, 1), (504893815226934776735621267, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_13, prime_oneHundredSixtyOneFC_29, prime_oneHundredSixtyOneFC_504893815226934776735621267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217660 : Nat.totient 190344968340554410829329217660 = 76046144166938022758352028224 := by
  rw [← show ((([(2, 2), (5, 1), (829, 1), (11480396160467696672456527, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_829, prime_oneHundredSixtyOneFC_11480396160467696672456527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217661 : Nat.totient 190344968340554410829329217661 = 126891926583686860256684647200 := by
  rw [← show ((([(3, 2), (26891, 1), (2515658779, 1), (312636878054861, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_26891, prime_oneHundredSixtyOneFC_2515658779, prime_oneHundredSixtyOneFC_312636878054861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217662 : Nat.totient 190344968340554410829329217662 = 95172279309787127833332217440 := by
  rw [← show ((([(2, 1), (497677, 1), (6984071, 1), (27381370965110893, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_497677, prime_oneHundredSixtyOneFC_6984071, prime_oneHundredSixtyOneFC_27381370965110893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217663 : Nat.totient 190344968340554410829329217663 = 163001973728242576080361143936 := by
  rw [← show ((([(7, 1), (1093, 1), (102983, 1), (58233839, 1), (4148415406349, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_1093, prime_oneHundredSixtyOneFC_102983, prime_oneHundredSixtyOneFC_58233839, prime_oneHundredSixtyOneFC_4148415406349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217664 : Nat.totient 190344968340554410829329217664 = 56228264329956840493041254400 := by
  rw [← show ((([(2, 7), (3, 1), (11, 1), (83, 1), (109, 1), (241, 1), (20667876537459905543, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_11, prime_oneHundredSixtyOneFC_83, prime_oneHundredSixtyOneFC_109, prime_oneHundredSixtyOneFC_241, prime_oneHundredSixtyOneFC_20667876537459905543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217665 : Nat.totient 190344968340554410829329217665 = 152237854227083346278751467520 := by
  rw [← show ((([(5, 1), (4493, 1), (72167, 1), (74699, 1), (1883881, 1), (834311197, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_4493, prime_oneHundredSixtyOneFC_72167, prime_oneHundredSixtyOneFC_74699, prime_oneHundredSixtyOneFC_1883881, prime_oneHundredSixtyOneFC_834311197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217666 : Nat.totient 190344968340554410829329217666 = 92600254858151086467005026944 := by
  rw [← show ((([(2, 1), (37, 1), (9054723493, 1), (284075963654540713, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_37, prime_oneHundredSixtyOneFC_9054723493, prime_oneHundredSixtyOneFC_284075963654540713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217667 : Nat.totient 190344968340554410829329217667 = 119432136997994924441932058112 := by
  rw [← show ((([(3, 1), (17, 1), (3732254281187341388810376817, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_17, prime_oneHundredSixtyOneFC_3732254281187341388810376817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217668 : Nat.totient 190344968340554410829329217668 = 93632372620268378555609280000 := by
  rw [← show ((([(2, 2), (67, 1), (821, 1), (17231, 1), (50205693148235096401, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_67, prime_oneHundredSixtyOneFC_821, prime_oneHundredSixtyOneFC_17231, prime_oneHundredSixtyOneFC_50205693148235096401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217669 : Nat.totient 190344968340554410829329217669 = 182069094928778167813568555536 := by
  rw [← show ((([(23, 1), (34858727, 1), (237411658455564283589, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_23, prime_oneHundredSixtyOneFC_34858727, prime_oneHundredSixtyOneFC_237411658455564283589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217670 : Nat.totient 190344968340554410829329217670 = 43473643265192353697177745408 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (7, 1), (1289, 1), (1723669, 1), (135985957393556749, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_1289, prime_oneHundredSixtyOneFC_1723669, prime_oneHundredSixtyOneFC_135985957393556749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217671 : Nat.totient 190344968340554410829329217671 = 190344968339350911649347794152 := by
  rw [← show ((([(158159636933, 1), (1203499021821786587, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_158159636933, prime_oneHundredSixtyOneFC_1203499021821786587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217672 : Nat.totient 190344968340554410829329217672 = 83227759436355774775577146944 := by
  rw [← show ((([(2, 3), (13, 1), (19, 1), (96328425273559924508769847, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_13, prime_oneHundredSixtyOneFC_19, prime_oneHundredSixtyOneFC_96328425273559924508769847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217673 : Nat.totient 190344968340554410829329217673 = 126892533402550953592280147520 := by
  rw [← show ((([(3, 1), (30859, 1), (9052809589, 1), (227119755515941, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_30859, prime_oneHundredSixtyOneFC_9052809589, prime_oneHundredSixtyOneFC_227119755515941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217674 : Nat.totient 190344968340554410829329217674 = 94533742665778700680338000576 := by
  rw [← show ((([(2, 1), (149, 1), (638741504498504734326608113, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_149, prime_oneHundredSixtyOneFC_638741504498504734326608113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217675 : Nat.totient 190344968340554410829329217675 = 138432704174519954343704115200 := by
  rw [← show ((([(5, 2), (11, 1), (1892295113, 1), (365779902132199649, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_11, prime_oneHundredSixtyOneFC_1892295113, prime_oneHundredSixtyOneFC_365779902132199649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217676 : Nat.totient 190344968340554410829329217676 = 62674435984755830563770624000 := by
  rw [← show ((([(2, 2), (3, 1), (157, 1), (173, 1), (12391, 1), (222601, 1), (211729285236823, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_157, prime_oneHundredSixtyOneFC_173, prime_oneHundredSixtyOneFC_12391, prime_oneHundredSixtyOneFC_222601, prime_oneHundredSixtyOneFC_211729285236823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217677 : Nat.totient 190344968340554410829329217677 = 163152830006184460174514151552 := by
  rw [← show ((([(7, 1), (33763383185377, 1), (805373625772843, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_33763383185377, prime_oneHundredSixtyOneFC_805373625772843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217678 : Nat.totient 190344968340554410829329217678 = 91241023065565930918578921600 := by
  rw [← show ((([(2, 1), (31, 1), (107, 1), (149371, 1), (192087739292377947377, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_31, prime_oneHundredSixtyOneFC_107, prime_oneHundredSixtyOneFC_149371, prime_oneHundredSixtyOneFC_192087739292377947377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217679 : Nat.totient 190344968340554410829329217679 = 126896645560369607219552811768 := by
  rw [← show ((([(3, 3), (7049813642242755956641822877, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_7049813642242755956641822877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217680 : Nat.totient 190344968340554410829329217680 = 76048725755090318918213896704 := by
  rw [← show ((([(2, 4), (5, 1), (853, 1), (30293503, 1), (92077365910501919, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_853, prime_oneHundredSixtyOneFC_30293503, prime_oneHundredSixtyOneFC_92077365910501919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217681 : Nat.totient 190344968340554410829329217681 = 190140032278653567468589240960 := by
  rw [← show ((([(929, 1), (4347191, 1), (47132118946340557079, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_929, prime_oneHundredSixtyOneFC_4347191, prime_oneHundredSixtyOneFC_47132118946340557079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217682 : Nat.totient 190344968340554410829329217682 = 63448322780165466485780660160 := by
  rw [← show ((([(2, 1), (3, 1), (3282280732531, 1), (9665279717140337, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_3282280732531, prime_oneHundredSixtyOneFC_9665279717140337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217683 : Nat.totient 190344968340554410829329217683 = 190339393070254518264809363520 := by
  rw [← show ((([(34141, 1), (19401299369, 1), (287365314175127, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_34141, prime_oneHundredSixtyOneFC_19401299369, prime_oneHundredSixtyOneFC_287365314175127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217684 : Nat.totient 190344968340554410829329217684 = 76748905930428266946067292160 := by
  rw [← show ((([(2, 2), (7, 2), (17, 1), (2657, 1), (21500316536914473447941, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_17, prime_oneHundredSixtyOneFC_2657, prime_oneHundredSixtyOneFC_21500316536914473447941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217685 : Nat.totient 190344968340554410829329217685 = 93708292106119094562131307072 := by
  rw [← show ((([(3, 1), (5, 1), (13, 1), (976128042772073901688867783, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_13, prime_oneHundredSixtyOneFC_976128042772073901688867783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217686 : Nat.totient 190344968340554410829329217686 = 86520440154725408027246135680 := by
  rw [← show ((([(2, 1), (11, 1), (1201015049369, 1), (7203943048028777, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_11, prime_oneHundredSixtyOneFC_1201015049369, prime_oneHundredSixtyOneFC_7203943048028777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217687 : Nat.totient 190344968340554410829329217687 = 187118782436477217425442281736 := by
  rw [← show ((([(59, 1), (3226185904077193403886935893, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_59, prime_oneHundredSixtyOneFC_3226185904077193403886935893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217688 : Nat.totient 190344968340554410829329217688 = 61260449580086974233892178688 := by
  rw [← show ((([(2, 3), (3, 2), (29, 1), (78432520189, 1), (1162290630024259, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_29, prime_oneHundredSixtyOneFC_78432520189, prime_oneHundredSixtyOneFC_1162290630024259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217689 : Nat.totient 190344968340554410829329217689 = 185582744941790497285161216000 := by
  rw [← show ((([(41, 1), (1553, 1), (2156311, 1), (360047533, 1), (3850479811, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_41, prime_oneHundredSixtyOneFC_1553, prime_oneHundredSixtyOneFC_2156311, prime_oneHundredSixtyOneFC_360047533, prime_oneHundredSixtyOneFC_3850479811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217690 : Nat.totient 190344968340554410829329217690 = 75681956516214177735731870976 := by
  rw [← show ((([(2, 1), (5, 1), (167, 1), (660277, 1), (712885559, 1), (242146916549, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_167, prime_oneHundredSixtyOneFC_660277, prime_oneHundredSixtyOneFC_712885559, prime_oneHundredSixtyOneFC_242146916549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217691 : Nat.totient 190344968340554410829329217691 = 102933867665871058428360493056 := by
  rw [← show ((([(3, 1), (7, 1), (19, 1), (937, 1), (1948313, 1), (261318517715367989, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_19, prime_oneHundredSixtyOneFC_937, prime_oneHundredSixtyOneFC_1948313, prime_oneHundredSixtyOneFC_261318517715367989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217692 : Nat.totient 190344968340554410829329217692 = 88917444032634142133292564480 := by
  rw [← show ((([(2, 2), (23, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_23, prime_oneHundredSixtyOneFC_43, prime_oneHundredSixtyOneFC_4282273, prime_oneHundredSixtyOneFC_32701811, prime_oneHundredSixtyOneFC_343588771969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217693 : Nat.totient 190344968340554410829329217693 = 190343055634054169287962162400 := by
  rw [← show ((([(99551, 1), (283340969, 1), (6748175973433547, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_99551, prime_oneHundredSixtyOneFC_283340969, prime_oneHundredSixtyOneFC_6748175973433547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217694 : Nat.totient 190344968340554410829329217694 = 63386782214927592355062750680 := by
  rw [← show ((([(2, 1), (3, 1), (1031, 1), (30770282628605627356826579, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_1031, prime_oneHundredSixtyOneFC_30770282628605627356826579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217695 : Nat.totient 190344968340554410829329217695 = 145493968562547912100803340800 := by
  rw [← show ((([(5, 1), (47, 1), (71, 1), (103, 1), (17467, 1), (17987, 1), (352533920183581, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_47, prime_oneHundredSixtyOneFC_71, prime_oneHundredSixtyOneFC_103, prime_oneHundredSixtyOneFC_17467, prime_oneHundredSixtyOneFC_17987, prime_oneHundredSixtyOneFC_352533920183581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217696 : Nat.totient 190344968340554410829329217696 = 95172484111895101709837841088 := by
  rw [← show ((([(2, 5), (1630165379, 1), (3648881479921507607, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_1630165379, prime_oneHundredSixtyOneFC_3648881479921507607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217697 : Nat.totient 190344968340554410829329217697 = 115360550401946204292129271680 := by
  rw [← show ((([(3, 2), (11, 1), (3163067, 1), (607851951249969725009, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_11, prime_oneHundredSixtyOneFC_3163067, prime_oneHundredSixtyOneFC_607851951249969725009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217698 : Nat.totient 190344968340554410829329217698 = 74455223336610790577978207232 := by
  rw [← show ((([(2, 1), (7, 1), (13, 1), (89, 1), (102211363, 1), (114969019264351177, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_7, prime_oneHundredSixtyOneFC_13, prime_oneHundredSixtyOneFC_89, prime_oneHundredSixtyOneFC_102211363, prime_oneHundredSixtyOneFC_114969019264351177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217699 : Nat.totient 190344968340554410829329217699 = 187695903751372346310533952000 := by
  rw [← show ((([(73, 1), (4513, 1), (577767631228367397774251, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_73, prime_oneHundredSixtyOneFC_4513, prime_oneHundredSixtyOneFC_577767631228367397774251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217700 : Nat.totient 190344968340554410829329217700 = 50711518999352635475474949120 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (1087, 1), (147107, 1), (515369, 1), (7699082468479, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_2, prime_oneHundredSixtyOneFC_3, prime_oneHundredSixtyOneFC_5, prime_oneHundredSixtyOneFC_1087, prime_oneHundredSixtyOneFC_147107, prime_oneHundredSixtyOneFC_515369, prime_oneHundredSixtyOneFC_7699082468479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyOneFC_190344968340554410829329217701 : Nat.totient 190344968340554410829329217701 = 177881376972508059526207257600 := by
  rw [← show ((([(17, 1), (151, 1), (2213, 1), (5592934027, 1), (5990932437253, 1)] : List FactorBlock).map factorBlockValue).prod) = 190344968340554410829329217701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyOneFC_17, prime_oneHundredSixtyOneFC_151, prime_oneHundredSixtyOneFC_2213, prime_oneHundredSixtyOneFC_5592934027, prime_oneHundredSixtyOneFC_5990932437253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixtyOneFC : certifiedKill 1 190344968340554410829329217599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixtyOneFC_190344968340554410829329217600, phi_oneHundredSixtyOneFC_190344968340554410829329217601, phi_oneHundredSixtyOneFC_190344968340554410829329217602,
    phi_oneHundredSixtyOneFC_190344968340554410829329217603, phi_oneHundredSixtyOneFC_190344968340554410829329217604, phi_oneHundredSixtyOneFC_190344968340554410829329217605,
    phi_oneHundredSixtyOneFC_190344968340554410829329217606, phi_oneHundredSixtyOneFC_190344968340554410829329217607, phi_oneHundredSixtyOneFC_190344968340554410829329217608,
    phi_oneHundredSixtyOneFC_190344968340554410829329217609, phi_oneHundredSixtyOneFC_190344968340554410829329217610, phi_oneHundredSixtyOneFC_190344968340554410829329217611,
    phi_oneHundredSixtyOneFC_190344968340554410829329217612, phi_oneHundredSixtyOneFC_190344968340554410829329217613, phi_oneHundredSixtyOneFC_190344968340554410829329217614,
    phi_oneHundredSixtyOneFC_190344968340554410829329217615, phi_oneHundredSixtyOneFC_190344968340554410829329217616, phi_oneHundredSixtyOneFC_190344968340554410829329217617,
    phi_oneHundredSixtyOneFC_190344968340554410829329217618, phi_oneHundredSixtyOneFC_190344968340554410829329217619, phi_oneHundredSixtyOneFC_190344968340554410829329217620,
    phi_oneHundredSixtyOneFC_190344968340554410829329217621, phi_oneHundredSixtyOneFC_190344968340554410829329217622, phi_oneHundredSixtyOneFC_190344968340554410829329217623,
    phi_oneHundredSixtyOneFC_190344968340554410829329217624, phi_oneHundredSixtyOneFC_190344968340554410829329217625, phi_oneHundredSixtyOneFC_190344968340554410829329217626,
    phi_oneHundredSixtyOneFC_190344968340554410829329217627, phi_oneHundredSixtyOneFC_190344968340554410829329217628, phi_oneHundredSixtyOneFC_190344968340554410829329217629,
    phi_oneHundredSixtyOneFC_190344968340554410829329217630, phi_oneHundredSixtyOneFC_190344968340554410829329217631, phi_oneHundredSixtyOneFC_190344968340554410829329217632,
    phi_oneHundredSixtyOneFC_190344968340554410829329217633, phi_oneHundredSixtyOneFC_190344968340554410829329217634, phi_oneHundredSixtyOneFC_190344968340554410829329217635,
    phi_oneHundredSixtyOneFC_190344968340554410829329217636, phi_oneHundredSixtyOneFC_190344968340554410829329217637, phi_oneHundredSixtyOneFC_190344968340554410829329217638,
    phi_oneHundredSixtyOneFC_190344968340554410829329217639, phi_oneHundredSixtyOneFC_190344968340554410829329217640, phi_oneHundredSixtyOneFC_190344968340554410829329217641,
    phi_oneHundredSixtyOneFC_190344968340554410829329217642, phi_oneHundredSixtyOneFC_190344968340554410829329217643, phi_oneHundredSixtyOneFC_190344968340554410829329217644,
    phi_oneHundredSixtyOneFC_190344968340554410829329217645, phi_oneHundredSixtyOneFC_190344968340554410829329217646, phi_oneHundredSixtyOneFC_190344968340554410829329217647,
    phi_oneHundredSixtyOneFC_190344968340554410829329217648, phi_oneHundredSixtyOneFC_190344968340554410829329217649, phi_oneHundredSixtyOneFC_190344968340554410829329217650,
    phi_oneHundredSixtyOneFC_190344968340554410829329217651, phi_oneHundredSixtyOneFC_190344968340554410829329217652, phi_oneHundredSixtyOneFC_190344968340554410829329217653,
    phi_oneHundredSixtyOneFC_190344968340554410829329217654, phi_oneHundredSixtyOneFC_190344968340554410829329217655, phi_oneHundredSixtyOneFC_190344968340554410829329217656,
    phi_oneHundredSixtyOneFC_190344968340554410829329217657, phi_oneHundredSixtyOneFC_190344968340554410829329217658, phi_oneHundredSixtyOneFC_190344968340554410829329217659,
    phi_oneHundredSixtyOneFC_190344968340554410829329217660, phi_oneHundredSixtyOneFC_190344968340554410829329217661, phi_oneHundredSixtyOneFC_190344968340554410829329217662,
    phi_oneHundredSixtyOneFC_190344968340554410829329217663, phi_oneHundredSixtyOneFC_190344968340554410829329217664, phi_oneHundredSixtyOneFC_190344968340554410829329217665,
    phi_oneHundredSixtyOneFC_190344968340554410829329217666, phi_oneHundredSixtyOneFC_190344968340554410829329217667, phi_oneHundredSixtyOneFC_190344968340554410829329217668,
    phi_oneHundredSixtyOneFC_190344968340554410829329217669, phi_oneHundredSixtyOneFC_190344968340554410829329217670, phi_oneHundredSixtyOneFC_190344968340554410829329217671,
    phi_oneHundredSixtyOneFC_190344968340554410829329217672, phi_oneHundredSixtyOneFC_190344968340554410829329217673, phi_oneHundredSixtyOneFC_190344968340554410829329217674,
    phi_oneHundredSixtyOneFC_190344968340554410829329217675, phi_oneHundredSixtyOneFC_190344968340554410829329217676, phi_oneHundredSixtyOneFC_190344968340554410829329217677,
    phi_oneHundredSixtyOneFC_190344968340554410829329217678, phi_oneHundredSixtyOneFC_190344968340554410829329217679, phi_oneHundredSixtyOneFC_190344968340554410829329217680,
    phi_oneHundredSixtyOneFC_190344968340554410829329217681, phi_oneHundredSixtyOneFC_190344968340554410829329217682, phi_oneHundredSixtyOneFC_190344968340554410829329217683,
    phi_oneHundredSixtyOneFC_190344968340554410829329217684, phi_oneHundredSixtyOneFC_190344968340554410829329217685, phi_oneHundredSixtyOneFC_190344968340554410829329217686,
    phi_oneHundredSixtyOneFC_190344968340554410829329217687, phi_oneHundredSixtyOneFC_190344968340554410829329217688, phi_oneHundredSixtyOneFC_190344968340554410829329217689,
    phi_oneHundredSixtyOneFC_190344968340554410829329217690, phi_oneHundredSixtyOneFC_190344968340554410829329217691, phi_oneHundredSixtyOneFC_190344968340554410829329217692,
    phi_oneHundredSixtyOneFC_190344968340554410829329217693, phi_oneHundredSixtyOneFC_190344968340554410829329217694, phi_oneHundredSixtyOneFC_190344968340554410829329217695,
    phi_oneHundredSixtyOneFC_190344968340554410829329217696, phi_oneHundredSixtyOneFC_190344968340554410829329217697, phi_oneHundredSixtyOneFC_190344968340554410829329217698,
    phi_oneHundredSixtyOneFC_190344968340554410829329217699, phi_oneHundredSixtyOneFC_190344968340554410829329217700, phi_oneHundredSixtyOneFC_190344968340554410829329217701]

end TotientTailPeriodKiller
end Erdos249257
