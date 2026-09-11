import Erdos249257.DiagonalPincerCertificatesT64
/- Kernel-checked off-diagonal certificate at a freely chosen position. -/
namespace Erdos249257
namespace TotientTailPeriodKiller
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private def oneHundredFiftyEightEZFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFiftyEightEZFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFiftyEightEZFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFiftyEightEZFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFiftyEightEZFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFiftyEightEZFastPow a n * oneHundredFiftyEightEZFastPow a n * a else oneHundredFiftyEightEZFastPow a n * oneHundredFiftyEightEZFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFiftyEightEZ_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1873 : Nat.Prime 1873 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1999 : Nat.Prime 1999 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2371 : Nat.Prime 2371 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2503 : Nat.Prime 2503 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2753 : Nat.Prime 2753 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2957 : Nat.Prime 2957 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3019 : Nat.Prime 3019 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3217 : Nat.Prime 3217 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3467 : Nat.Prime 3467 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3637 : Nat.Prime 3637 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3659 : Nat.Prime 3659 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3671 : Nat.Prime 3671 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3709 : Nat.Prime 3709 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3769 : Nat.Prime 3769 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3803 : Nat.Prime 3803 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3943 : Nat.Prime 3943 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4013 : Nat.Prime 4013 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4177 : Nat.Prime 4177 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4217 : Nat.Prime 4217 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4219 : Nat.Prime 4219 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4229 : Nat.Prime 4229 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4337 : Nat.Prime 4337 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4373 : Nat.Prime 4373 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4517 : Nat.Prime 4517 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4793 : Nat.Prime 4793 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5119 : Nat.Prime 5119 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5227 : Nat.Prime 5227 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5273 : Nat.Prime 5273 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5303 : Nat.Prime 5303 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5743 : Nat.Prime 5743 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5791 : Nat.Prime 5791 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5821 : Nat.Prime 5821 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_6269 : Nat.Prime 6269 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_6481 : Nat.Prime 6481 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_6791 : Nat.Prime 6791 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_6827 : Nat.Prime 6827 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_6869 : Nat.Prime 6869 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_7207 : Nat.Prime 7207 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_7321 : Nat.Prime 7321 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_7517 : Nat.Prime 7517 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_7639 : Nat.Prime 7639 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_8017 : Nat.Prime 8017 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_8243 : Nat.Prime 8243 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_8297 : Nat.Prime 8297 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_8387 : Nat.Prime 8387 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_8627 : Nat.Prime 8627 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_8923 : Nat.Prime 8923 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_9059 : Nat.Prime 9059 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_9157 : Nat.Prime 9157 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_9403 : Nat.Prime 9403 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_9421 : Nat.Prime 9421 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_10039 : Nat.Prime 10039 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_10163 : Nat.Prime 10163 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_10601 : Nat.Prime 10601 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_10627 : Nat.Prime 10627 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_10663 : Nat.Prime 10663 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_10979 : Nat.Prime 10979 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_11617 : Nat.Prime 11617 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_11677 : Nat.Prime 11677 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_12253 : Nat.Prime 12253 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_12721 : Nat.Prime 12721 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_12763 : Nat.Prime 12763 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_12823 : Nat.Prime 12823 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_12829 : Nat.Prime 12829 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_13841 : Nat.Prime 13841 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_13907 : Nat.Prime 13907 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_13931 : Nat.Prime 13931 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_14033 : Nat.Prime 14033 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_14321 : Nat.Prime 14321 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_14389 : Nat.Prime 14389 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_14489 : Nat.Prime 14489 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_14503 : Nat.Prime 14503 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_14591 : Nat.Prime 14591 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_14851 : Nat.Prime 14851 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_14923 : Nat.Prime 14923 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_15139 : Nat.Prime 15139 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_15217 : Nat.Prime 15217 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_15581 : Nat.Prime 15581 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_15649 : Nat.Prime 15649 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_16649 : Nat.Prime 16649 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_17291 : Nat.Prime 17291 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_17359 : Nat.Prime 17359 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_18049 : Nat.Prime 18049 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_19759 : Nat.Prime 19759 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_20089 : Nat.Prime 20089 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_20201 : Nat.Prime 20201 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_21313 : Nat.Prime 21313 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_23819 : Nat.Prime 23819 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_24001 : Nat.Prime 24001 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_24019 : Nat.Prime 24019 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_27017 : Nat.Prime 27017 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_27997 : Nat.Prime 27997 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_28463 : Nat.Prime 28463 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_29027 : Nat.Prime 29027 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_29401 : Nat.Prime 29401 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_30817 : Nat.Prime 30817 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_32063 : Nat.Prime 32063 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_33161 : Nat.Prime 33161 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_34843 : Nat.Prime 34843 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_36011 : Nat.Prime 36011 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_36209 : Nat.Prime 36209 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_37871 : Nat.Prime 37871 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_39251 : Nat.Prime 39251 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_40507 : Nat.Prime 40507 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_43159 : Nat.Prime 43159 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_43397 : Nat.Prime 43397 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_43969 : Nat.Prime 43969 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_45677 : Nat.Prime 45677 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_49307 : Nat.Prime 49307 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_50341 : Nat.Prime 50341 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_51511 : Nat.Prime 51511 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_52529 : Nat.Prime 52529 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_55381 : Nat.Prime 55381 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_57529 : Nat.Prime 57529 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_58337 : Nat.Prime 58337 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_59219 : Nat.Prime 59219 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_61223 : Nat.Prime 61223 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_62927 : Nat.Prime 62927 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_63311 : Nat.Prime 63311 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_63853 : Nat.Prime 63853 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_64747 : Nat.Prime 64747 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_67121 : Nat.Prime 67121 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_68161 : Nat.Prime 68161 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_68447 : Nat.Prime 68447 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_68521 : Nat.Prime 68521 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_71161 : Nat.Prime 71161 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_71867 : Nat.Prime 71867 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_72559 : Nat.Prime 72559 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_74177 : Nat.Prime 74177 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_74609 : Nat.Prime 74609 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_78007 : Nat.Prime 78007 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_86291 : Nat.Prime 86291 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_87323 : Nat.Prime 87323 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_91253 : Nat.Prime 91253 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_92941 : Nat.Prime 92941 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_93557 : Nat.Prime 93557 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_93581 : Nat.Prime 93581 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_95231 : Nat.Prime 95231 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_95401 : Nat.Prime 95401 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_95957 : Nat.Prime 95957 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_98911 : Nat.Prime 98911 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_99679 : Nat.Prime 99679 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_102763 : Nat.Prime 102763 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_104231 : Nat.Prime 104231 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_104281 : Nat.Prime 104281 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_105229 : Nat.Prime 105229 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_108203 : Nat.Prime 108203 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_110281 : Nat.Prime 110281 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_111127 : Nat.Prime 111127 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_118471 : Nat.Prime 118471 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_127447 : Nat.Prime 127447 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_151429 : Nat.Prime 151429 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_152597 : Nat.Prime 152597 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_163003 : Nat.Prime 163003 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_170207 : Nat.Prime 170207 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_179813 : Nat.Prime 179813 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_187751 : Nat.Prime 187751 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_188171 : Nat.Prime 188171 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_196181 : Nat.Prime 196181 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_196477 : Nat.Prime 196477 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_204791 : Nat.Prime 204791 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_205033 : Nat.Prime 205033 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_218417 : Nat.Prime 218417 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_247991 : Nat.Prime 247991 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_261467 : Nat.Prime 261467 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_282847 : Nat.Prime 282847 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_297467 : Nat.Prime 297467 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_307093 : Nat.Prime 307093 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_327917 : Nat.Prime 327917 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_344321 : Nat.Prime 344321 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_345011 : Nat.Prime 345011 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_345271 : Nat.Prime 345271 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_369827 : Nat.Prime 369827 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_377231 : Nat.Prime 377231 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_381841 : Nat.Prime 381841 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_396679 : Nat.Prime 396679 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_400601 : Nat.Prime 400601 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_405157 : Nat.Prime 405157 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_407893 : Nat.Prime 407893 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_409841 : Nat.Prime 409841 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_410953 : Nat.Prime 410953 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_426563 : Nat.Prime 426563 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_426941 : Nat.Prime 426941 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_468883 : Nat.Prime 468883 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_501863 : Nat.Prime 501863 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_572183 : Nat.Prime 572183 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_581351 : Nat.Prime 581351 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_590839 : Nat.Prime 590839 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_599941 : Nat.Prime 599941 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_625927 : Nat.Prime 625927 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_633427 : Nat.Prime 633427 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_638527 : Nat.Prime 638527 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_689621 : Nat.Prime 689621 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_751021 : Nat.Prime 751021 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_769903 : Nat.Prime 769903 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_832427 : Nat.Prime 832427 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_833563 : Nat.Prime 833563 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_835453 : Nat.Prime 835453 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_838993 : Nat.Prime 838993 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_849223 : Nat.Prime 849223 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_896647 : Nat.Prime 896647 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_905767 : Nat.Prime 905767 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1087433 : Nat.Prime 1087433 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1145387 : Nat.Prime 1145387 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1147507 : Nat.Prime 1147507 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1253323 : Nat.Prime 1253323 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1270249 : Nat.Prime 1270249 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1299821 : Nat.Prime 1299821 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1429403 : Nat.Prime 1429403 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1486241 : Nat.Prime 1486241 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1569047 : Nat.Prime 1569047 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1636333 : Nat.Prime 1636333 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1684247 : Nat.Prime 1684247 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1691243 : Nat.Prime 1691243 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1697317 : Nat.Prime 1697317 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_1841923 : Nat.Prime 1841923 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2003611 : Nat.Prime 2003611 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2038019 : Nat.Prime 2038019 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2038159 : Nat.Prime 2038159 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2227859 : Nat.Prime 2227859 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2301119 : Nat.Prime 2301119 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2397007 : Nat.Prime 2397007 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2624899 : Nat.Prime 2624899 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2785963 : Nat.Prime 2785963 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2884513 : Nat.Prime 2884513 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_2990983 : Nat.Prime 2990983 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3128249 : Nat.Prime 3128249 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3201749 : Nat.Prime 3201749 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3205871 : Nat.Prime 3205871 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3439747 : Nat.Prime 3439747 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3446137 : Nat.Prime 3446137 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3472387 : Nat.Prime 3472387 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3786011 : Nat.Prime 3786011 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3794951 : Nat.Prime 3794951 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_3836927 : Nat.Prime 3836927 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4211371 : Nat.Prime 4211371 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4299683 : Nat.Prime 4299683 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4680667 : Nat.Prime 4680667 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4695259 : Nat.Prime 4695259 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4700627 : Nat.Prime 4700627 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4775171 : Nat.Prime 4775171 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_4793209 : Nat.Prime 4793209 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5095157 : Nat.Prime 5095157 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5167823 : Nat.Prime 5167823 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5638159 : Nat.Prime 5638159 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5828441 : Nat.Prime 5828441 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5905037 : Nat.Prime 5905037 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_5971919 : Nat.Prime 5971919 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_6744239 : Nat.Prime 6744239 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_7752539 : Nat.Prime 7752539 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_7811941 : Nat.Prime 7811941 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_7987669 : Nat.Prime 7987669 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_8425331 : Nat.Prime 8425331 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_8561011 : Nat.Prime 8561011 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_8780201 : Nat.Prime 8780201 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_9180469 : Nat.Prime 9180469 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_9391483 : Nat.Prime 9391483 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_9527149 : Nat.Prime 9527149 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_10216901 : Nat.Prime 10216901 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_11018303 : Nat.Prime 11018303 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_12251741 : Nat.Prime 12251741 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_12764209 : Nat.Prime 12764209 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_12844253 : Nat.Prime 12844253 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_12994451 : Nat.Prime 12994451 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_13151651 : Nat.Prime 13151651 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_13209857 : Nat.Prime 13209857 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_13278583 : Nat.Prime 13278583 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_13766891 : Nat.Prime 13766891 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_15052813 : Nat.Prime 15052813 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_15259007 : Nat.Prime 15259007 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_15274559 : Nat.Prime 15274559 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_18344311 : Nat.Prime 18344311 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_19877191 : Nat.Prime 19877191 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_20251619 : Nat.Prime 20251619 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_21791491 : Nat.Prime 21791491 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_23552941 : Nat.Prime 23552941 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_25784533 : Nat.Prime 25784533 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_27232319 : Nat.Prime 27232319 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_28811219 : Nat.Prime 28811219 := by norm_num

private theorem prime_oneHundredFiftyEightEZ_31633883 : Nat.Prime 31633883 := by
  apply lucas_primality 31633883 (5 : ZMod 31633883)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (953, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (953, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) = 31633883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_953
      · exact prime_oneHundredFiftyEightEZ_2371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 31633883) ^ 15816941 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 31633883) ^ 4519126 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 31633883) ^ 33194 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 31633883) ^ 13342 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_35891797 : Nat.Prime 35891797 := by
  apply lucas_primality 35891797 (5 : ZMod 35891797)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2990983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2990983, 1)] : List FactorBlock).map factorBlockValue).prod) = 35891797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_2990983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 35891797) ^ 17945898 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 35891797) ^ 11963932 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 35891797) ^ 12 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_37808359 : Nat.Prime 37808359 := by
  apply lucas_primality 37808359 (3 : ZMod 37808359)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (229, 1), (3931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (229, 1), (3931, 1)] : List FactorBlock).map factorBlockValue).prod) = 37808359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_229
      · exact prime_oneHundredFiftyEightEZ_3931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37808359) ^ 18904179 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 37808359) ^ 12602786 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 37808359) ^ 5401194 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 37808359) ^ 165102 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 37808359) ^ 9618 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_40388681 : Nat.Prime 40388681 := by
  apply lucas_primality 40388681 (3 : ZMod 40388681)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 2), (2797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 2), (2797, 1)] : List FactorBlock).map factorBlockValue).prod) = 40388681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_2797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40388681) ^ 20194340 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 40388681) ^ 8077736 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 40388681) ^ 2125720 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 40388681) ^ 14440 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_44452963 : Nat.Prime 44452963 := by
  apply lucas_primality 44452963 (3 : ZMod 44452963)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (10163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (10163, 1)] : List FactorBlock).map factorBlockValue).prod) = 44452963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_10163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 44452963) ^ 22226481 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 44452963) ^ 14817654 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 44452963) ^ 4374 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_46457093 : Nat.Prime 46457093 := by
  apply lucas_primality 46457093 (5 : ZMod 46457093)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (83, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (83, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod) = 46457093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_83
      · exact prime_oneHundredFiftyEightEZ_12721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 46457093) ^ 23228546 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 46457093) ^ 4223372 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 46457093) ^ 559724 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 46457093) ^ 3652 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_49965107 : Nat.Prime 49965107 := by
  apply lucas_primality 49965107 (2 : ZMod 49965107)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3637, 1), (6869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3637, 1), (6869, 1)] : List FactorBlock).map factorBlockValue).prod) = 49965107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3637
      · exact prime_oneHundredFiftyEightEZ_6869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 49965107) ^ 24982553 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 49965107) ^ 13738 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 49965107) ^ 7274 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_52303261 : Nat.Prime 52303261 := by
  apply lucas_primality 52303261 (7 : ZMod 52303261)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (839, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (839, 1), (1039, 1)] : List FactorBlock).map factorBlockValue).prod) = 52303261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_839
      · exact prime_oneHundredFiftyEightEZ_1039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 52303261) ^ 26151630 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 52303261) ^ 17434420 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 52303261) ^ 10460652 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 52303261) ^ 62340 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 52303261) ^ 50340 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_55500139 : Nat.Prime 55500139 := by
  apply lucas_primality 55500139 (2 : ZMod 55500139)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 2), (47, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 2), (47, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 55500139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_47
      · exact prime_oneHundredFiftyEightEZ_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55500139) ^ 27750069 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 55500139) ^ 18500046 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 55500139) ^ 3264714 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 55500139) ^ 1180854 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 55500139) ^ 244494 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_56044717 : Nat.Prime 56044717 := by
  apply lucas_primality 56044717 (5 : ZMod 56044717)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (17, 1), (3019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (17, 1), (3019, 1)] : List FactorBlock).map factorBlockValue).prod) = 56044717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_3019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 56044717) ^ 28022358 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 56044717) ^ 18681572 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 56044717) ^ 8006388 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 56044717) ^ 4311132 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 56044717) ^ 3296748 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 56044717) ^ 18564 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_56348899 : Nat.Prime 56348899 := by
  apply lucas_primality 56348899 (2 : ZMod 56348899)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9391483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9391483, 1)] : List FactorBlock).map factorBlockValue).prod) = 56348899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_9391483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 56348899) ^ 28174449 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 56348899) ^ 18782966 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 56348899) ^ 6 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_57301759 : Nat.Prime 57301759 := by
  apply lucas_primality 57301759 (6 : ZMod 57301759)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (131, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (131, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) = 57301759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_131
      · exact prime_oneHundredFiftyEightEZ_1279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 57301759) ^ 28650879 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 57301759) ^ 19100586 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 57301759) ^ 3015882 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 57301759) ^ 437418 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 57301759) ^ 44802 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_1811
      · exact prime_oneHundredFiftyEightEZ_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_60195563 : Nat.Prime 60195563 := by
  apply lucas_primality 60195563 (2 : ZMod 60195563)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4299683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4299683, 1)] : List FactorBlock).map factorBlockValue).prod) = 60195563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_4299683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60195563) ^ 30097781 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 60195563) ^ 8599366 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 60195563) ^ 14 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_67269331 : Nat.Prime 67269331 := by
  apply lucas_primality 67269331 (3 : ZMod 67269331)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (20201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (20201, 1)] : List FactorBlock).map factorBlockValue).prod) = 67269331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_37
      · exact prime_oneHundredFiftyEightEZ_20201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67269331) ^ 33634665 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 67269331) ^ 22423110 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 67269331) ^ 13453866 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 67269331) ^ 1818090 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 67269331) ^ 3330 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_67321999 : Nat.Prime 67321999 := by
  apply lucas_primality 67321999 (33 : ZMod 67321999)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (239, 1), (15649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (239, 1), (15649, 1)] : List FactorBlock).map factorBlockValue).prod) = 67321999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_239
      · exact prime_oneHundredFiftyEightEZ_15649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (33 : ZMod 67321999) ^ 33660999 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (33 : ZMod 67321999) ^ 22440666 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (33 : ZMod 67321999) ^ 281682 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (33 : ZMod 67321999) ^ 4302 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_68887619 : Nat.Prime 68887619 := by
  apply lucas_primality 68887619 (2 : ZMod 68887619)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (73, 1), (10039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (73, 1), (10039, 1)] : List FactorBlock).map factorBlockValue).prod) = 68887619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_47
      · exact prime_oneHundredFiftyEightEZ_73
      · exact prime_oneHundredFiftyEightEZ_10039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68887619) ^ 34443809 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 68887619) ^ 1465694 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 68887619) ^ 943666 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 68887619) ^ 6862 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_80777363 : Nat.Prime 80777363 := by
  apply lucas_primality 80777363 (2 : ZMod 80777363)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (40388681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (40388681, 1)] : List FactorBlock).map factorBlockValue).prod) = 80777363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_40388681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 80777363) ^ 40388681 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 80777363) ^ 2 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_84611287 : Nat.Prime 84611287 := by
  apply lucas_primality 84611287 (3 : ZMod 84611287)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4700627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4700627, 1)] : List FactorBlock).map factorBlockValue).prod) = 84611287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_4700627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 84611287) ^ 42305643 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 84611287) ^ 28203762 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 84611287) ^ 18 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_90316879 : Nat.Prime 90316879 := by
  apply lucas_primality 90316879 (3 : ZMod 90316879)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15052813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15052813, 1)] : List FactorBlock).map factorBlockValue).prod) = 90316879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_15052813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 90316879) ^ 45158439 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 90316879) ^ 30105626 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 90316879) ^ 6 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_102333389 : Nat.Prime 102333389 := by
  apply lucas_primality 102333389 (2 : ZMod 102333389)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (381841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (381841, 1)] : List FactorBlock).map factorBlockValue).prod) = 102333389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_67
      · exact prime_oneHundredFiftyEightEZ_381841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 102333389) ^ 51166694 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 102333389) ^ 1527364 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 102333389) ^ 268 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_111999617 : Nat.Prime 111999617 := by
  apply lucas_primality 111999617 (3 : ZMod 111999617)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (857, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (857, 1), (1021, 1)] : List FactorBlock).map factorBlockValue).prod) = 111999617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_857
      · exact prime_oneHundredFiftyEightEZ_1021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 111999617) ^ 55999808 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 111999617) ^ 130688 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 111999617) ^ 109696 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_121769497 : Nat.Prime 121769497 := by
  apply lucas_primality 121769497 (5 : ZMod 121769497)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1691243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1691243, 1)] : List FactorBlock).map factorBlockValue).prod) = 121769497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_1691243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 121769497) ^ 60884748 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 121769497) ^ 40589832 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 121769497) ^ 72 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_135012643 : Nat.Prime 135012643 := by
  apply lucas_primality 135012643 (2 : ZMod 135012643)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (293, 1), (1259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (293, 1), (1259, 1)] : List FactorBlock).map factorBlockValue).prod) = 135012643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_61
      · exact prime_oneHundredFiftyEightEZ_293
      · exact prime_oneHundredFiftyEightEZ_1259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135012643) ^ 67506321 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 135012643) ^ 45004214 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 135012643) ^ 2213322 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 135012643) ^ 460794 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 135012643) ^ 107238 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_151037687 : Nat.Prime 151037687 := by
  apply lucas_primality 151037687 (5 : ZMod 151037687)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (1841923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (1841923, 1)] : List FactorBlock).map factorBlockValue).prod) = 151037687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_41
      · exact prime_oneHundredFiftyEightEZ_1841923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 151037687) ^ 75518843 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 151037687) ^ 3683846 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 151037687) ^ 82 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_151522417 : Nat.Prime 151522417 := by
  apply lucas_primality 151522417 (11 : ZMod 151522417)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (55381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (55381, 1)] : List FactorBlock).map factorBlockValue).prod) = 151522417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_55381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 151522417) ^ 75761208 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 151522417) ^ 50507472 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 151522417) ^ 7974864 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 151522417) ^ 2736 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_152324737 : Nat.Prime 152324737 := by
  apply lucas_primality 152324737 (5 : ZMod 152324737)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (396679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (396679, 1)] : List FactorBlock).map factorBlockValue).prod) = 152324737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_396679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 152324737) ^ 76162368 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 152324737) ^ 50774912 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 152324737) ^ 384 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_185272081 : Nat.Prime 185272081 := by
  apply lucas_primality 185272081 (19 : ZMod 185272081)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (110281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (110281, 1)] : List FactorBlock).map factorBlockValue).prod) = 185272081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_110281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 185272081) ^ 92636040 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 185272081) ^ 61757360 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 185272081) ^ 37054416 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 185272081) ^ 26467440 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 185272081) ^ 1680 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_187810361 : Nat.Prime 187810361 := by
  apply lucas_primality 187810361 (3 : ZMod 187810361)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (4695259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (4695259, 1)] : List FactorBlock).map factorBlockValue).prod) = 187810361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_4695259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 187810361) ^ 93905180 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 187810361) ^ 37562072 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 187810361) ^ 40 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_210773789 : Nat.Prime 210773789 := by
  apply lucas_primality 210773789 (2 : ZMod 210773789)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (61, 1), (20089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (61, 1), (20089, 1)] : List FactorBlock).map factorBlockValue).prod) = 210773789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_43
      · exact prime_oneHundredFiftyEightEZ_61
      · exact prime_oneHundredFiftyEightEZ_20089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 210773789) ^ 105386894 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 210773789) ^ 4901716 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 210773789) ^ 3455308 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 210773789) ^ 10492 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_212581333 : Nat.Prime 212581333 := by
  apply lucas_primality 212581333 (2 : ZMod 212581333)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5905037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5905037, 1)] : List FactorBlock).map factorBlockValue).prod) = 212581333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5905037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 212581333) ^ 106290666 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 212581333) ^ 70860444 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 212581333) ^ 36 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_218871871 : Nat.Prime 218871871 := by
  apply lucas_primality 218871871 (11 : ZMod 218871871)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (79, 2), (167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (79, 2), (167, 1)] : List FactorBlock).map factorBlockValue).prod) = 218871871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_79
      · exact prime_oneHundredFiftyEightEZ_167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 218871871) ^ 109435935 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 218871871) ^ 72957290 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 218871871) ^ 43774374 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 218871871) ^ 31267410 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 218871871) ^ 2770530 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 218871871) ^ 1310610 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_222000557 : Nat.Prime 222000557 := by
  apply lucas_primality 222000557 (2 : ZMod 222000557)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (55500139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (55500139, 1)] : List FactorBlock).map factorBlockValue).prod) = 222000557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_55500139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 222000557) ^ 111000278 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 222000557) ^ 4 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_244319137 : Nat.Prime 244319137 := by
  apply lucas_primality 244319137 (5 : ZMod 244319137)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (971, 1), (2621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (971, 1), (2621, 1)] : List FactorBlock).map factorBlockValue).prod) = 244319137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_971
      · exact prime_oneHundredFiftyEightEZ_2621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 244319137) ^ 122159568 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 244319137) ^ 81439712 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 244319137) ^ 251616 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 244319137) ^ 93216 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_249610709 : Nat.Prime 249610709 := by
  apply lucas_primality 249610709 (2 : ZMod 249610709)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (463, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (463, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) = 249610709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_53
      · exact prime_oneHundredFiftyEightEZ_463
      · exact prime_oneHundredFiftyEightEZ_2543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 249610709) ^ 124805354 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 249610709) ^ 4709636 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 249610709) ^ 539116 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 249610709) ^ 98156 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_271011371 : Nat.Prime 271011371 := by
  apply lucas_primality 271011371 (2 : ZMod 271011371)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (43, 1), (179, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (43, 1), (179, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) = 271011371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_43
      · exact prime_oneHundredFiftyEightEZ_179
      · exact prime_oneHundredFiftyEightEZ_503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 271011371) ^ 135505685 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271011371) ^ 54202274 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271011371) ^ 38715910 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271011371) ^ 6302590 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271011371) ^ 1514030 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 271011371) ^ 538790 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_274252331 : Nat.Prime 274252331 := by
  apply lucas_primality 274252331 (2 : ZMod 274252331)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (17, 2), (8627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (17, 2), (8627, 1)] : List FactorBlock).map factorBlockValue).prod) = 274252331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_8627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 274252331) ^ 137126165 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 274252331) ^ 54850466 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 274252331) ^ 24932030 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 274252331) ^ 16132490 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 274252331) ^ 31790 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_279596423 : Nat.Prime 279596423 := by
  apply lucas_primality 279596423 (5 : ZMod 279596423)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (293, 1), (68161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (293, 1), (68161, 1)] : List FactorBlock).map factorBlockValue).prod) = 279596423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_293
      · exact prime_oneHundredFiftyEightEZ_68161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 279596423) ^ 139798211 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 279596423) ^ 39942346 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 279596423) ^ 954254 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 279596423) ^ 4102 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_305491181 : Nat.Prime 305491181 := by
  apply lucas_primality 305491181 (2 : ZMod 305491181)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (15274559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (15274559, 1)] : List FactorBlock).map factorBlockValue).prod) = 305491181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_15274559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 305491181) ^ 152745590 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 305491181) ^ 61098236 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 305491181) ^ 20 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_336939373 : Nat.Prime 336939373 := by
  apply lucas_primality 336939373 (2 : ZMod 336939373)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (11, 1), (31, 1), (1307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (11, 1), (31, 1), (1307, 1)] : List FactorBlock).map factorBlockValue).prod) = 336939373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_31
      · exact prime_oneHundredFiftyEightEZ_1307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 336939373) ^ 168469686 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 336939373) ^ 112313124 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 336939373) ^ 48134196 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 336939373) ^ 30630852 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 336939373) ^ 10869012 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 336939373) ^ 257796 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_399720857 : Nat.Prime 399720857 := by
  apply lucas_primality 399720857 (3 : ZMod 399720857)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (49965107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (49965107, 1)] : List FactorBlock).map factorBlockValue).prod) = 399720857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_49965107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 399720857) ^ 199860428 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 399720857) ^ 8 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_403357067 : Nat.Prime 403357067 := by
  apply lucas_primality 403357067 (2 : ZMod 403357067)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (28811219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (28811219, 1)] : List FactorBlock).map factorBlockValue).prod) = 403357067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_28811219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 403357067) ^ 201678533 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 403357067) ^ 57622438 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 403357067) ^ 14 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_412732993 : Nat.Prime 412732993 := by
  apply lucas_primality 412732993 (5 : ZMod 412732993)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (307093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (307093, 1)] : List FactorBlock).map factorBlockValue).prod) = 412732993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_307093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 412732993) ^ 206366496 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 412732993) ^ 137577664 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 412732993) ^ 58961856 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 412732993) ^ 1344 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_492950779 : Nat.Prime 492950779 := by
  apply lucas_primality 492950779 (2 : ZMod 492950779)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (37, 1), (83, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (37, 1), (83, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) = 492950779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_31
      · exact prime_oneHundredFiftyEightEZ_37
      · exact prime_oneHundredFiftyEightEZ_83
      · exact prime_oneHundredFiftyEightEZ_863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 492950779) ^ 246475389 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 492950779) ^ 164316926 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 492950779) ^ 15901638 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 492950779) ^ 13322994 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 492950779) ^ 5939166 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 492950779) ^ 571206 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_507667723 : Nat.Prime 507667723 := by
  apply lucas_primality 507667723 (3 : ZMod 507667723)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (84611287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (84611287, 1)] : List FactorBlock).map factorBlockValue).prod) = 507667723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_84611287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 507667723) ^ 253833861 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 507667723) ^ 169222574 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 507667723) ^ 6 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_540246799 : Nat.Prime 540246799 := by
  apply lucas_primality 540246799 (6 : ZMod 540246799)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (19, 1), (17359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (19, 1), (17359, 1)] : List FactorBlock).map factorBlockValue).prod) = 540246799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_17359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 540246799) ^ 270123399 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 540246799) ^ 180082266 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 540246799) ^ 77178114 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 540246799) ^ 41557446 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 540246799) ^ 28434042 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 540246799) ^ 31122 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_559192847 : Nat.Prime 559192847 := by
  apply lucas_primality 559192847 (5 : ZMod 559192847)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (279596423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (279596423, 1)] : List FactorBlock).map factorBlockValue).prod) = 559192847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_279596423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 559192847) ^ 279596423 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 559192847) ^ 2 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_580995139 : Nat.Prime 580995139 := by
  apply lucas_primality 580995139 (2 : ZMod 580995139)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (239, 1), (405157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (239, 1), (405157, 1)] : List FactorBlock).map factorBlockValue).prod) = 580995139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_239
      · exact prime_oneHundredFiftyEightEZ_405157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 580995139) ^ 290497569 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 580995139) ^ 193665046 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 580995139) ^ 2430942 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 580995139) ^ 1434 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_592365419 : Nat.Prime 592365419 := by
  apply lucas_primality 592365419 (2 : ZMod 592365419)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (383, 1), (14591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (383, 1), (14591, 1)] : List FactorBlock).map factorBlockValue).prod) = 592365419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_53
      · exact prime_oneHundredFiftyEightEZ_383
      · exact prime_oneHundredFiftyEightEZ_14591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 592365419) ^ 296182709 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 592365419) ^ 11176706 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 592365419) ^ 1546646 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 592365419) ^ 40598 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_604698043 : Nat.Prime 604698043 := by
  apply lucas_primality 604698043 (3 : ZMod 604698043)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (7752539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (7752539, 1)] : List FactorBlock).map factorBlockValue).prod) = 604698043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_7752539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 604698043) ^ 302349021 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 604698043) ^ 201566014 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 604698043) ^ 46515234 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 604698043) ^ 78 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_647367397 : Nat.Prime 647367397 := by
  apply lucas_primality 647367397 (2 : ZMod 647367397)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (79, 1), (52529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (79, 1), (52529, 1)] : List FactorBlock).map factorBlockValue).prod) = 647367397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_79
      · exact prime_oneHundredFiftyEightEZ_52529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 647367397) ^ 323683698 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 647367397) ^ 215789132 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 647367397) ^ 49797492 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 647367397) ^ 8194524 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 647367397) ^ 12324 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_676402619 : Nat.Prime 676402619 := by
  apply lucas_primality 676402619 (2 : ZMod 676402619)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1987, 1), (170207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1987, 1), (170207, 1)] : List FactorBlock).map factorBlockValue).prod) = 676402619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_1987
      · exact prime_oneHundredFiftyEightEZ_170207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 676402619) ^ 338201309 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 676402619) ^ 340414 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 676402619) ^ 3974 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_17203
      · exact prime_oneHundredFiftyEightEZ_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_756043133 : Nat.Prime 756043133 := by
  apply lucas_primality 756043133 (2 : ZMod 756043133)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 2), (947, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 2), (947, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod) = 756043133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_947
      · exact prime_oneHundredFiftyEightEZ_1181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 756043133) ^ 378021566 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 756043133) ^ 58157164 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 756043133) ^ 798356 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 756043133) ^ 640172 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_894355387 : Nat.Prime 894355387 := by
  apply lucas_primality 894355387 (3 : ZMod 894355387)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (47, 1), (103, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (47, 1), (103, 1), (751, 1)] : List FactorBlock).map factorBlockValue).prod) = 894355387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_41
      · exact prime_oneHundredFiftyEightEZ_47
      · exact prime_oneHundredFiftyEightEZ_103
      · exact prime_oneHundredFiftyEightEZ_751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 894355387) ^ 447177693 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 894355387) ^ 298118462 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 894355387) ^ 21813546 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 894355387) ^ 19028838 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 894355387) ^ 8683062 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 894355387) ^ 1190886 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_908452877 : Nat.Prime 908452877 := by
  apply lucas_primality 908452877 (2 : ZMod 908452877)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1109, 1), (204791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1109, 1), (204791, 1)] : List FactorBlock).map factorBlockValue).prod) = 908452877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_1109
      · exact prime_oneHundredFiftyEightEZ_204791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 908452877) ^ 454226438 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 908452877) ^ 819164 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 908452877) ^ 4436 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_951055351 : Nat.Prime 951055351 := by
  apply lucas_primality 951055351 (29 : ZMod 951055351)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (905767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (905767, 1)] : List FactorBlock).map factorBlockValue).prod) = 951055351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_905767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 951055351) ^ 475527675 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (29 : ZMod 951055351) ^ 317018450 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (29 : ZMod 951055351) ^ 190211070 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (29 : ZMod 951055351) ^ 135865050 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (29 : ZMod 951055351) ^ 1050 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_977276549 : Nat.Prime 977276549 := by
  apply lucas_primality 977276549 (2 : ZMod 977276549)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (244319137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (244319137, 1)] : List FactorBlock).map factorBlockValue).prod) = 977276549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_244319137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 977276549) ^ 488638274 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 977276549) ^ 4 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1197045779 : Nat.Prime 1197045779 := by
  apply lucas_primality 1197045779 (2 : ZMod 1197045779)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18049, 1), (33161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18049, 1), (33161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1197045779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_18049
      · exact prime_oneHundredFiftyEightEZ_33161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1197045779) ^ 598522889 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1197045779) ^ 66322 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1197045779) ^ 36098 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1252703029 : Nat.Prime 1252703029 := by
  apply lucas_primality 1252703029 (2 : ZMod 1252703029)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (139, 1), (751021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (139, 1), (751021, 1)] : List FactorBlock).map factorBlockValue).prod) = 1252703029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_139
      · exact prime_oneHundredFiftyEightEZ_751021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1252703029) ^ 626351514 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252703029) ^ 417567676 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252703029) ^ 9012252 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1252703029) ^ 1668 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1308409489 : Nat.Prime 1308409489 := by
  apply lucas_primality 1308409489 (22 : ZMod 1308409489)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (17, 1), (59, 1), (9059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (17, 1), (59, 1), (9059, 1)] : List FactorBlock).map factorBlockValue).prod) = 1308409489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_59
      · exact prime_oneHundredFiftyEightEZ_9059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 1308409489) ^ 654204744 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 1308409489) ^ 436136496 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 1308409489) ^ 76965264 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 1308409489) ^ 22176432 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 1308409489) ^ 144432 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1323316609 : Nat.Prime 1323316609 := by
  apply lucas_primality 1323316609 (7 : ZMod 1323316609)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (3446137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (3446137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1323316609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_3446137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1323316609) ^ 661658304 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1323316609) ^ 441105536 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 1323316609) ^ 384 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1500097997 : Nat.Prime 1500097997 := by
  apply lucas_primality 1500097997 (5 : ZMod 1500097997)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 2), (41, 1), (17291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 2), (41, 1), (17291, 1)] : List FactorBlock).map factorBlockValue).prod) = 1500097997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_23
      · exact prime_oneHundredFiftyEightEZ_41
      · exact prime_oneHundredFiftyEightEZ_17291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1500097997) ^ 750048998 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1500097997) ^ 65221652 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1500097997) ^ 36587756 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1500097997) ^ 86756 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1672555861 : Nat.Prime 1672555861 := by
  apply lucas_primality 1672555861 (2 : ZMod 1672555861)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (23, 1), (29, 1), (13931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (23, 1), (29, 1), (13931, 1)] : List FactorBlock).map factorBlockValue).prod) = 1672555861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_23
      · exact prime_oneHundredFiftyEightEZ_29
      · exact prime_oneHundredFiftyEightEZ_13931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1672555861) ^ 836277930 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1672555861) ^ 557518620 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1672555861) ^ 334511172 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1672555861) ^ 72719820 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1672555861) ^ 57674340 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1672555861) ^ 120060 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1682553137 : Nat.Prime 1682553137 := by
  apply lucas_primality 1682553137 (3 : ZMod 1682553137)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (151, 1), (63311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (151, 1), (63311, 1)] : List FactorBlock).map factorBlockValue).prod) = 1682553137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_151
      · exact prime_oneHundredFiftyEightEZ_63311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1682553137) ^ 841276568 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682553137) ^ 152959376 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682553137) ^ 11142736 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682553137) ^ 26576 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1826370709 : Nat.Prime 1826370709 := by
  apply lucas_primality 1826370709 (6 : ZMod 1826370709)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (1569047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (1569047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1826370709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_97
      · exact prime_oneHundredFiftyEightEZ_1569047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1826370709) ^ 913185354 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1826370709) ^ 608790236 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1826370709) ^ 18828564 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 1826370709) ^ 1164 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1980986257 : Nat.Prime 1980986257 := by
  apply lucas_primality 1980986257 (5 : ZMod 1980986257)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (317, 1), (43397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (317, 1), (43397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1980986257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_317
      · exact prime_oneHundredFiftyEightEZ_43397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1980986257) ^ 990493128 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1980986257) ^ 660328752 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1980986257) ^ 6249168 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1980986257) ^ 45648 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2188982767 : Nat.Prime 2188982767 := by
  apply lucas_primality 2188982767 (3 : ZMod 2188982767)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (179, 1), (2038159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (179, 1), (2038159, 1)] : List FactorBlock).map factorBlockValue).prod) = 2188982767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_179
      · exact prime_oneHundredFiftyEightEZ_2038159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2188982767) ^ 1094491383 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2188982767) ^ 729660922 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2188982767) ^ 12228954 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2188982767) ^ 1074 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2394091559 : Nat.Prime 2394091559 := by
  apply lucas_primality 2394091559 (13 : ZMod 2394091559)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1197045779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1197045779, 1)] : List FactorBlock).map factorBlockValue).prod) = 2394091559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_1197045779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 2394091559) ^ 1197045779 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 2394091559) ^ 2 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2492066279 : Nat.Prime 2492066279 := by
  apply lucas_primality 2492066279 (23 : ZMod 2492066279)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (5638159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (5638159, 1)] : List FactorBlock).map factorBlockValue).prod) = 2492066279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_5638159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 2492066279) ^ 1246033139 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (23 : ZMod 2492066279) ^ 191697406 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (23 : ZMod 2492066279) ^ 146592134 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (23 : ZMod 2492066279) ^ 442 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2557739263 : Nat.Prime 2557739263 := by
  apply lucas_primality 2557739263 (3 : ZMod 2557739263)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (97, 1), (311, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (97, 1), (311, 1), (1087, 1)] : List FactorBlock).map factorBlockValue).prod) = 2557739263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_97
      · exact prime_oneHundredFiftyEightEZ_311
      · exact prime_oneHundredFiftyEightEZ_1087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2557739263) ^ 1278869631 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2557739263) ^ 852579754 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2557739263) ^ 196749174 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2557739263) ^ 26368446 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2557739263) ^ 8224242 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2557739263) ^ 2353026 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2610719317 : Nat.Prime 2610719317 := by
  apply lucas_primality 2610719317 (2 : ZMod 2610719317)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (29, 1), (833563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (29, 1), (833563, 1)] : List FactorBlock).map factorBlockValue).prod) = 2610719317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_29
      · exact prime_oneHundredFiftyEightEZ_833563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2610719317) ^ 1305359658 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2610719317) ^ 870239772 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2610719317) ^ 90024804 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2610719317) ^ 3132 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2848874491 : Nat.Prime 2848874491 := by
  apply lucas_primality 2848874491 (3 : ZMod 2848874491)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (7, 1), (11, 1), (45677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (7, 1), (11, 1), (45677, 1)] : List FactorBlock).map factorBlockValue).prod) = 2848874491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_45677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2848874491) ^ 1424437245 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2848874491) ^ 949624830 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2848874491) ^ 569774898 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2848874491) ^ 406982070 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2848874491) ^ 258988590 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2848874491) ^ 62370 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2954178191 : Nat.Prime 2954178191 := by
  apply lucas_primality 2954178191 (17 : ZMod 2954178191)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (12844253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (12844253, 1)] : List FactorBlock).map factorBlockValue).prod) = 2954178191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_23
      · exact prime_oneHundredFiftyEightEZ_12844253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 2954178191) ^ 1477089095 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (17 : ZMod 2954178191) ^ 590835638 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (17 : ZMod 2954178191) ^ 128442530 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (17 : ZMod 2954178191) ^ 230 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_4940452667 : Nat.Prime 4940452667 := by
  apply lucas_primality 4940452667 (2 : ZMod 4940452667)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5791, 1), (426563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5791, 1), (426563, 1)] : List FactorBlock).map factorBlockValue).prod) = 4940452667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5791
      · exact prime_oneHundredFiftyEightEZ_426563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4940452667) ^ 2470226333 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4940452667) ^ 853126 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4940452667) ^ 11582 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_5118268117 : Nat.Prime 5118268117 := by
  apply lucas_primality 5118268117 (5 : ZMod 5118268117)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (29, 1), (79, 1), (14321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (29, 1), (79, 1), (14321, 1)] : List FactorBlock).map factorBlockValue).prod) = 5118268117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_29
      · exact prime_oneHundredFiftyEightEZ_79
      · exact prime_oneHundredFiftyEightEZ_14321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5118268117) ^ 2559134058 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5118268117) ^ 1706089372 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5118268117) ^ 393712932 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5118268117) ^ 176492004 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5118268117) ^ 64788204 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 5118268117) ^ 357396 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_5322503159 : Nat.Prime 5322503159 := by
  apply lucas_primality 5322503159 (14 : ZMod 5322503159)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (157, 1), (859, 1), (2819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (157, 1), (859, 1), (2819, 1)] : List FactorBlock).map factorBlockValue).prod) = 5322503159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_157
      · exact prime_oneHundredFiftyEightEZ_859
      · exact prime_oneHundredFiftyEightEZ_2819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 5322503159) ^ 2661251579 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 5322503159) ^ 760357594 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 5322503159) ^ 33901294 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 5322503159) ^ 6196162 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 5322503159) ^ 1888082 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_5540628461 : Nat.Prime 5540628461 := by
  apply lucas_primality 5540628461 (2 : ZMod 5540628461)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (73, 1), (3794951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (73, 1), (3794951, 1)] : List FactorBlock).map factorBlockValue).prod) = 5540628461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_73
      · exact prime_oneHundredFiftyEightEZ_3794951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5540628461) ^ 2770314230 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5540628461) ^ 1108125692 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5540628461) ^ 75899020 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5540628461) ^ 1460 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_31
      · exact prime_oneHundredFiftyEightEZ_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_6416103259 : Nat.Prime 6416103259 := by
  apply lucas_primality 6416103259 (11 : ZMod 6416103259)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2753, 1), (43159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2753, 1), (43159, 1)] : List FactorBlock).map factorBlockValue).prod) = 6416103259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_2753
      · exact prime_oneHundredFiftyEightEZ_43159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 6416103259) ^ 3208051629 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 6416103259) ^ 2138701086 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 6416103259) ^ 2330586 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 6416103259) ^ 148662 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_7197260459 : Nat.Prime 7197260459 := by
  apply lucas_primality 7197260459 (2 : ZMod 7197260459)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (41, 1), (631, 1), (7321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (41, 1), (631, 1), (7321, 1)] : List FactorBlock).map factorBlockValue).prod) = 7197260459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_41
      · exact prime_oneHundredFiftyEightEZ_631
      · exact prime_oneHundredFiftyEightEZ_7321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7197260459) ^ 3598630229 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7197260459) ^ 378803182 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7197260459) ^ 175542938 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7197260459) ^ 11406118 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 7197260459) ^ 983098 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_7818212393 : Nat.Prime 7818212393 := by
  apply lucas_primality 7818212393 (3 : ZMod 7818212393)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (977276549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (977276549, 1)] : List FactorBlock).map factorBlockValue).prod) = 7818212393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_977276549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 7818212393) ^ 3909106196 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 7818212393) ^ 8 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_8042281217 : Nat.Prime 8042281217 := by
  apply lucas_primality 8042281217 (3 : ZMod 8042281217)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (67, 1), (468883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (67, 1), (468883, 1)] : List FactorBlock).map factorBlockValue).prod) = 8042281217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_67
      · exact prime_oneHundredFiftyEightEZ_468883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8042281217) ^ 4021140608 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8042281217) ^ 120034048 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 8042281217) ^ 17152 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_9308831339 : Nat.Prime 9308831339 := by
  apply lucas_primality 9308831339 (2 : ZMod 9308831339)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (137, 1), (457, 1), (4373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (137, 1), (457, 1), (4373, 1)] : List FactorBlock).map factorBlockValue).prod) = 9308831339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_137
      · exact prime_oneHundredFiftyEightEZ_457
      · exact prime_oneHundredFiftyEightEZ_4373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9308831339) ^ 4654415669 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9308831339) ^ 547578314 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9308831339) ^ 67947674 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9308831339) ^ 20369434 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 9308831339) ^ 2128706 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_10230957053 : Nat.Prime 10230957053 := by
  apply lucas_primality 10230957053 (2 : ZMod 10230957053)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2557739263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2557739263, 1)] : List FactorBlock).map factorBlockValue).prod) = 10230957053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_2557739263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 10230957053) ^ 5115478526 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 10230957053) ^ 4 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_10865971267 : Nat.Prime 10865971267 := by
  apply lucas_primality 10865971267 (2 : ZMod 10865971267)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (2473, 1), (15581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (2473, 1), (15581, 1)] : List FactorBlock).map factorBlockValue).prod) = 10865971267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_47
      · exact prime_oneHundredFiftyEightEZ_2473
      · exact prime_oneHundredFiftyEightEZ_15581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10865971267) ^ 5432985633 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 10865971267) ^ 3621990422 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 10865971267) ^ 231190878 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 10865971267) ^ 4393842 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 10865971267) ^ 697386 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_14292425687 : Nat.Prime 14292425687 := by
  apply lucas_primality 14292425687 (7 : ZMod 14292425687)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (269, 1), (345011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (269, 1), (345011, 1)] : List FactorBlock).map factorBlockValue).prod) = 14292425687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_269
      · exact prime_oneHundredFiftyEightEZ_345011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14292425687) ^ 7146212843 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14292425687) ^ 2041775098 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14292425687) ^ 1299311426 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14292425687) ^ 53131694 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14292425687) ^ 41426 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_16975148767 : Nat.Prime 16975148767 := by
  apply lucas_primality 16975148767 (5 : ZMod 16975148767)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (60195563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (60195563, 1)] : List FactorBlock).map factorBlockValue).prod) = 16975148767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_47
      · exact prime_oneHundredFiftyEightEZ_60195563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16975148767) ^ 8487574383 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 16975148767) ^ 5658382922 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 16975148767) ^ 361173378 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 16975148767) ^ 282 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_19002515507 : Nat.Prime 19002515507 := by
  apply lucas_primality 19002515507 (2 : ZMod 19002515507)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (59, 1), (167, 1), (74177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (59, 1), (167, 1), (74177, 1)] : List FactorBlock).map factorBlockValue).prod) = 19002515507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_59
      · exact prime_oneHundredFiftyEightEZ_167
      · exact prime_oneHundredFiftyEightEZ_74177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19002515507) ^ 9501257753 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 19002515507) ^ 1461731962 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 19002515507) ^ 322076534 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 19002515507) ^ 113787518 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 19002515507) ^ 256178 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_19554018689 : Nat.Prime 19554018689 := by
  apply lucas_primality 19554018689 (3 : ZMod 19554018689)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (4219, 1), (36209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (4219, 1), (36209, 1)] : List FactorBlock).map factorBlockValue).prod) = 19554018689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_4219
      · exact prime_oneHundredFiftyEightEZ_36209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19554018689) ^ 9777009344 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 19554018689) ^ 4634752 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 19554018689) ^ 540032 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_19756369289 : Nat.Prime 19756369289 := by
  apply lucas_primality 19756369289 (3 : ZMod 19756369289)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (269, 1), (9180469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (269, 1), (9180469, 1)] : List FactorBlock).map factorBlockValue).prod) = 19756369289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_269
      · exact prime_oneHundredFiftyEightEZ_9180469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19756369289) ^ 9878184644 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 19756369289) ^ 73443752 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 19756369289) ^ 2152 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_21566025457 : Nat.Prime 21566025457 := by
  apply lucas_primality 21566025457 (5 : ZMod 21566025457)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (79, 1), (83, 1), (68521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (79, 1), (83, 1), (68521, 1)] : List FactorBlock).map factorBlockValue).prod) = 21566025457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_79
      · exact prime_oneHundredFiftyEightEZ_83
      · exact prime_oneHundredFiftyEightEZ_68521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21566025457) ^ 10783012728 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21566025457) ^ 7188675152 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21566025457) ^ 272987664 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21566025457) ^ 259831632 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 21566025457) ^ 314736 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_22002051713 : Nat.Prime 22002051713 := by
  apply lucas_primality 22002051713 (3 : ZMod 22002051713)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (17, 1), (23, 1), (499, 1), (881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (17, 1), (23, 1), (499, 1), (881, 1)] : List FactorBlock).map factorBlockValue).prod) = 22002051713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_23
      · exact prime_oneHundredFiftyEightEZ_499
      · exact prime_oneHundredFiftyEightEZ_881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22002051713) ^ 11001025856 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 22002051713) ^ 1294238336 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 22002051713) ^ 956610944 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 22002051713) ^ 44092288 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 22002051713) ^ 24973952 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_29590681259 : Nat.Prime 29590681259 := by
  apply lucas_primality 29590681259 (2 : ZMod 29590681259)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1999, 1), (2503, 1), (2957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1999, 1), (2503, 1), (2957, 1)] : List FactorBlock).map factorBlockValue).prod) = 29590681259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_1999
      · exact prime_oneHundredFiftyEightEZ_2503
      · exact prime_oneHundredFiftyEightEZ_2957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 29590681259) ^ 14795340629 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 29590681259) ^ 14802742 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 29590681259) ^ 11822086 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 29590681259) ^ 10006994 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_33433273721 : Nat.Prime 33433273721 := by
  apply lucas_primality 33433273721 (6 : ZMod 33433273721)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (11, 1), (17, 1), (638527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (11, 1), (17, 1), (638527, 1)] : List FactorBlock).map factorBlockValue).prod) = 33433273721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_638527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 33433273721) ^ 16716636860 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 33433273721) ^ 6686654744 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 33433273721) ^ 4776181960 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 33433273721) ^ 3039388520 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 33433273721) ^ 1966663160 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 33433273721) ^ 52360 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_41292103603 : Nat.Prime 41292103603 := by
  apply lucas_primality 41292103603 (3 : ZMod 41292103603)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (222000557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (222000557, 1)] : List FactorBlock).map factorBlockValue).prod) = 41292103603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_31
      · exact prime_oneHundredFiftyEightEZ_222000557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 41292103603) ^ 20646051801 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 41292103603) ^ 13764034534 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 41292103603) ^ 1332003342 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 41292103603) ^ 186 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_42644088733 : Nat.Prime 42644088733 := by
  apply lucas_primality 42644088733 (2 : ZMod 42644088733)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (507667723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (507667723, 1)] : List FactorBlock).map factorBlockValue).prod) = 42644088733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_507667723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42644088733) ^ 21322044366 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 42644088733) ^ 14214696244 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 42644088733) ^ 6092012676 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 42644088733) ^ 84 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_44004103427 : Nat.Prime 44004103427 := by
  apply lucas_primality 44004103427 (2 : ZMod 44004103427)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22002051713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22002051713, 1)] : List FactorBlock).map factorBlockValue).prod) = 44004103427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_22002051713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 44004103427) ^ 22002051713 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 44004103427) ^ 2 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_46913015939 : Nat.Prime 46913015939 := by
  apply lucas_primality 46913015939 (2 : ZMod 46913015939)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (733, 1), (1684247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (733, 1), (1684247, 1)] : List FactorBlock).map factorBlockValue).prod) = 46913015939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_733
      · exact prime_oneHundredFiftyEightEZ_1684247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46913015939) ^ 23456507969 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 46913015939) ^ 2469106102 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 46913015939) ^ 64001386 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 46913015939) ^ 27854 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_50815221361 : Nat.Prime 50815221361 := by
  apply lucas_primality 50815221361 (19 : ZMod 50815221361)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (5227, 1), (40507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (5227, 1), (40507, 1)] : List FactorBlock).map factorBlockValue).prod) = 50815221361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_5227
      · exact prime_oneHundredFiftyEightEZ_40507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 50815221361) ^ 25407610680 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 50815221361) ^ 16938407120 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 50815221361) ^ 10163044272 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 50815221361) ^ 9721680 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 50815221361) ^ 1254480 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_50859313903 : Nat.Prime 50859313903 := by
  apply lucas_primality 50859313903 (3 : ZMod 50859313903)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37871, 1), (74609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37871, 1), (74609, 1)] : List FactorBlock).map factorBlockValue).prod) = 50859313903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_37871
      · exact prime_oneHundredFiftyEightEZ_74609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50859313903) ^ 25429656951 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 50859313903) ^ 16953104634 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 50859313903) ^ 1342962 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 50859313903) ^ 681678 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_58415620223 : Nat.Prime 58415620223 := by
  apply lucas_primality 58415620223 (5 : ZMod 58415620223)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (643, 1), (769903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (643, 1), (769903, 1)] : List FactorBlock).map factorBlockValue).prod) = 58415620223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_59
      · exact prime_oneHundredFiftyEightEZ_643
      · exact prime_oneHundredFiftyEightEZ_769903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 58415620223) ^ 29207810111 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 58415620223) ^ 990095258 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 58415620223) ^ 90848554 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 58415620223) ^ 75874 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_64764130373 : Nat.Prime 64764130373 := by
  apply lucas_primality 64764130373 (2 : ZMod 64764130373)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (305491181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (305491181, 1)] : List FactorBlock).map factorBlockValue).prod) = 64764130373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_53
      · exact prime_oneHundredFiftyEightEZ_305491181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 64764130373) ^ 32382065186 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64764130373) ^ 1221964724 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 64764130373) ^ 212 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_71549123839 : Nat.Prime 71549123839 := by
  apply lucas_primality 71549123839 (6 : ZMod 71549123839)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (1103, 1), (72559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (1103, 1), (72559, 1)] : List FactorBlock).map factorBlockValue).prod) = 71549123839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_149
      · exact prime_oneHundredFiftyEightEZ_1103
      · exact prime_oneHundredFiftyEightEZ_72559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 71549123839) ^ 35774561919 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 71549123839) ^ 23849707946 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 71549123839) ^ 480195462 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 71549123839) ^ 64867746 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 71549123839) ^ 986082 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_75498035633 : Nat.Prime 75498035633 := by
  apply lucas_primality 75498035633 (3 : ZMod 75498035633)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (233, 1), (20251619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (233, 1), (20251619, 1)] : List FactorBlock).map factorBlockValue).prod) = 75498035633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_233
      · exact prime_oneHundredFiftyEightEZ_20251619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 75498035633) ^ 37749017816 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 75498035633) ^ 324025904 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 75498035633) ^ 3728 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_80075433121 : Nat.Prime 80075433121 := by
  apply lucas_primality 80075433121 (11 : ZMod 80075433121)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (19, 1), (8780201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (19, 1), (8780201, 1)] : List FactorBlock).map factorBlockValue).prod) = 80075433121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_8780201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 80075433121) ^ 40037716560 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 80075433121) ^ 26691811040 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 80075433121) ^ 16015086624 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 80075433121) ^ 4214496480 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 80075433121) ^ 9120 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_94222975673 : Nat.Prime 94222975673 := by
  apply lucas_primality 94222975673 (3 : ZMod 94222975673)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1682553137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1682553137, 1)] : List FactorBlock).map factorBlockValue).prod) = 94222975673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_1682553137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 94222975673) ^ 47111487836 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 94222975673) ^ 13460425096 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 94222975673) ^ 56 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_103932780911 : Nat.Prime 103932780911 := by
  apply lucas_primality 103932780911 (7 : ZMod 103932780911)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2153, 1), (689621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2153, 1), (689621, 1)] : List FactorBlock).map factorBlockValue).prod) = 103932780911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_2153
      · exact prime_oneHundredFiftyEightEZ_689621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 103932780911) ^ 51966390455 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 103932780911) ^ 20786556182 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 103932780911) ^ 14847540130 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 103932780911) ^ 48273470 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 103932780911) ^ 150710 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_123199578701 : Nat.Prime 123199578701 := by
  apply lucas_primality 123199578701 (2 : ZMod 123199578701)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (111999617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (111999617, 1)] : List FactorBlock).map factorBlockValue).prod) = 123199578701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_111999617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 123199578701) ^ 61599789350 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 123199578701) ^ 24639915740 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 123199578701) ^ 11199961700 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 123199578701) ^ 1100 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_129161432903 : Nat.Prime 129161432903 := by
  apply lucas_primality 129161432903 (5 : ZMod 129161432903)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (157, 1), (4229, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (157, 1), (4229, 2)] : List FactorBlock).map factorBlockValue).prod) = 129161432903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_23
      · exact prime_oneHundredFiftyEightEZ_157
      · exact prime_oneHundredFiftyEightEZ_4229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 129161432903) ^ 64580716451 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 129161432903) ^ 5615714474 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 129161432903) ^ 822684286 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 129161432903) ^ 30541838 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_129423492893 : Nat.Prime 129423492893 := by
  apply lucas_primality 129423492893 (2 : ZMod 129423492893)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (557, 1), (4177, 1), (13907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (557, 1), (4177, 1), (13907, 1)] : List FactorBlock).map factorBlockValue).prod) = 129423492893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_557
      · exact prime_oneHundredFiftyEightEZ_4177
      · exact prime_oneHundredFiftyEightEZ_13907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 129423492893) ^ 64711746446 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 129423492893) ^ 232358156 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 129423492893) ^ 30984796 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 129423492893) ^ 9306356 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_138902213999 : Nat.Prime 138902213999 := by
  apply lucas_primality 138902213999 (19 : ZMod 138902213999)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (41, 1), (977, 1), (91253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (41, 1), (977, 1), (91253, 1)] : List FactorBlock).map factorBlockValue).prod) = 138902213999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_41
      · exact prime_oneHundredFiftyEightEZ_977
      · exact prime_oneHundredFiftyEightEZ_91253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 138902213999) ^ 69451106999 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 138902213999) ^ 7310642842 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 138902213999) ^ 3387858878 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 138902213999) ^ 142172174 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 138902213999) ^ 1522166 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_152755276489 : Nat.Prime 152755276489 := by
  apply lucas_primality 152755276489 (11 : ZMod 152755276489)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (63853, 1), (99679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (63853, 1), (99679, 1)] : List FactorBlock).map factorBlockValue).prod) = 152755276489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_63853
      · exact prime_oneHundredFiftyEightEZ_99679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 152755276489) ^ 76377638244 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 152755276489) ^ 50918425496 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 152755276489) ^ 2392296 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 152755276489) ^ 1532472 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_207865561823 : Nat.Prime 207865561823 := by
  apply lucas_primality 207865561823 (5 : ZMod 207865561823)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103932780911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103932780911, 1)] : List FactorBlock).map factorBlockValue).prod) = 207865561823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_103932780911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 207865561823) ^ 103932780911 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 207865561823) ^ 2 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_240339536431 : Nat.Prime 240339536431 := by
  apply lucas_primality 240339536431 (6 : ZMod 240339536431)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (67321999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (67321999, 1)] : List FactorBlock).map factorBlockValue).prod) = 240339536431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_67321999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 240339536431) ^ 120169768215 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 240339536431) ^ 80113178810 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 240339536431) ^ 48067907286 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 240339536431) ^ 34334219490 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 240339536431) ^ 14137619790 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 240339536431) ^ 3570 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_240518981569 : Nat.Prime 240518981569 := by
  apply lucas_primality 240518981569 (7 : ZMod 240518981569)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (1252703029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (1252703029, 1)] : List FactorBlock).map factorBlockValue).prod) = 240518981569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_1252703029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 240518981569) ^ 120259490784 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 240518981569) ^ 80172993856 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 240518981569) ^ 192 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_283044625439 : Nat.Prime 283044625439 := by
  apply lucas_primality 283044625439 (7 : ZMod 283044625439)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (937, 1), (151037687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (937, 1), (151037687, 1)] : List FactorBlock).map factorBlockValue).prod) = 283044625439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_937
      · exact prime_oneHundredFiftyEightEZ_151037687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 283044625439) ^ 141522312719 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 283044625439) ^ 302075374 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 283044625439) ^ 1874 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_294025907029 : Nat.Prime 294025907029 := by
  apply lucas_primality 294025907029 (2 : ZMod 294025907029)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1747, 1), (2003611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1747, 1), (2003611, 1)] : List FactorBlock).map factorBlockValue).prod) = 294025907029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_1747
      · exact prime_oneHundredFiftyEightEZ_2003611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 294025907029) ^ 147012953514 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 294025907029) ^ 98008635676 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 294025907029) ^ 42003701004 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 294025907029) ^ 168303324 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 294025907029) ^ 146748 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_385355308027 : Nat.Prime 385355308027 := by
  apply lucas_primality 385355308027 (2 : ZMod 385355308027)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (4940452667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (4940452667, 1)] : List FactorBlock).map factorBlockValue).prod) = 385355308027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_4940452667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 385355308027) ^ 192677654013 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 385355308027) ^ 128451769342 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 385355308027) ^ 29642716002 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 385355308027) ^ 78 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_553216207043 : Nat.Prime 553216207043 := by
  apply lucas_primality 553216207043 (2 : ZMod 553216207043)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (79, 1), (1097, 1), (187751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (79, 1), (1097, 1), (187751, 1)] : List FactorBlock).map factorBlockValue).prod) = 553216207043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_79
      · exact prime_oneHundredFiftyEightEZ_1097
      · exact prime_oneHundredFiftyEightEZ_187751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 553216207043) ^ 276608103521 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 553216207043) ^ 32542129826 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 553216207043) ^ 7002736798 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 553216207043) ^ 504299186 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 553216207043) ^ 2946542 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_559652608213 : Nat.Prime 559652608213 := by
  apply lucas_primality 559652608213 (5 : ZMod 559652608213)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (383, 1), (121769497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (383, 1), (121769497, 1)] : List FactorBlock).map factorBlockValue).prod) = 559652608213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_383
      · exact prime_oneHundredFiftyEightEZ_121769497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 559652608213) ^ 279826304106 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 559652608213) ^ 186550869404 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 559652608213) ^ 1461233964 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 559652608213) ^ 4596 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_607384847983 : Nat.Prime 607384847983 := by
  apply lucas_primality 607384847983 (3 : ZMod 607384847983)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (9403, 1), (51511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (9403, 1), (51511, 1)] : List FactorBlock).map factorBlockValue).prod) = 607384847983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_9403
      · exact prime_oneHundredFiftyEightEZ_51511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 607384847983) ^ 303692423991 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 607384847983) ^ 202461615994 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 607384847983) ^ 55216804362 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 607384847983) ^ 31967623578 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 607384847983) ^ 64594794 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 607384847983) ^ 11791362 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_629711430577 : Nat.Prime 629711430577 := by
  apply lucas_primality 629711430577 (5 : ZMod 629711430577)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (557, 1), (23552941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (557, 1), (23552941, 1)] : List FactorBlock).map factorBlockValue).prod) = 629711430577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_557
      · exact prime_oneHundredFiftyEightEZ_23552941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 629711430577) ^ 314855715288 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 629711430577) ^ 209903810192 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 629711430577) ^ 1130541168 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 629711430577) ^ 26736 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_652891134631 : Nat.Prime 652891134631 := by
  apply lucas_primality 652891134631 (7 : ZMod 652891134631)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (523, 1), (849223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (523, 1), (849223, 1)] : List FactorBlock).map factorBlockValue).prod) = 652891134631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_523
      · exact prime_oneHundredFiftyEightEZ_849223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 652891134631) ^ 326445567315 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 652891134631) ^ 217630378210 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 652891134631) ^ 130578226926 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 652891134631) ^ 93270162090 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 652891134631) ^ 1248357810 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 652891134631) ^ 768810 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_950882401187 : Nat.Prime 950882401187 := by
  apply lucas_primality 950882401187 (2 : ZMod 950882401187)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (39251, 1), (111127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (39251, 1), (111127, 1)] : List FactorBlock).map factorBlockValue).prod) = 950882401187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_109
      · exact prime_oneHundredFiftyEightEZ_39251
      · exact prime_oneHundredFiftyEightEZ_111127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 950882401187) ^ 475441200593 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 950882401187) ^ 8723691754 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 950882401187) ^ 24225686 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 950882401187) ^ 8556718 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1096034094119 : Nat.Prime 1096034094119 := by
  apply lucas_primality 1096034094119 (17 : ZMod 1096034094119)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (727, 1), (3673, 1), (8923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (727, 1), (3673, 1), (8923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1096034094119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_23
      · exact prime_oneHundredFiftyEightEZ_727
      · exact prime_oneHundredFiftyEightEZ_3673
      · exact prime_oneHundredFiftyEightEZ_8923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1096034094119) ^ 548017047059 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (17 : ZMod 1096034094119) ^ 47653656266 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (17 : ZMod 1096034094119) ^ 1507612234 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (17 : ZMod 1096034094119) ^ 298402966 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (17 : ZMod 1096034094119) ^ 122832466 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1151792954303 : Nat.Prime 1151792954303 := by
  apply lucas_primality 1151792954303 (5 : ZMod 1151792954303)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (10865971267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (10865971267, 1)] : List FactorBlock).map factorBlockValue).prod) = 1151792954303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_53
      · exact prime_oneHundredFiftyEightEZ_10865971267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1151792954303) ^ 575896477151 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1151792954303) ^ 21731942534 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1151792954303) ^ 106 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1749532260277 : Nat.Prime 1749532260277 := by
  apply lucas_primality 1749532260277 (5 : ZMod 1749532260277)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23, 1), (29401, 1), (71867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23, 1), (29401, 1), (71867, 1)] : List FactorBlock).map factorBlockValue).prod) = 1749532260277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_23
      · exact prime_oneHundredFiftyEightEZ_29401
      · exact prime_oneHundredFiftyEightEZ_71867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1749532260277) ^ 874766130138 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1749532260277) ^ 583177420092 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1749532260277) ^ 76066620012 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1749532260277) ^ 59505876 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 1749532260277) ^ 24344028 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2172663506219 : Nat.Prime 2172663506219 := by
  apply lucas_primality 2172663506219 (2 : ZMod 2172663506219)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59219, 1), (18344311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59219, 1), (18344311, 1)] : List FactorBlock).map factorBlockValue).prod) = 2172663506219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_59219
      · exact prime_oneHundredFiftyEightEZ_18344311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2172663506219) ^ 1086331753109 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2172663506219) ^ 36688622 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2172663506219) ^ 118438 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_3145025406661 : Nat.Prime 3145025406661 := by
  apply lucas_primality 3145025406661 (2 : ZMod 3145025406661)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (127, 1), (412732993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (127, 1), (412732993, 1)] : List FactorBlock).map factorBlockValue).prod) = 3145025406661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_127
      · exact prime_oneHundredFiftyEightEZ_412732993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3145025406661) ^ 1572512703330 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3145025406661) ^ 1048341802220 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3145025406661) ^ 629005081332 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3145025406661) ^ 24763979580 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3145025406661) ^ 7620 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_3396535505269 : Nat.Prime 3396535505269 := by
  apply lucas_primality 3396535505269 (2 : ZMod 3396535505269)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (283044625439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (283044625439, 1)] : List FactorBlock).map factorBlockValue).prod) = 3396535505269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_283044625439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3396535505269) ^ 1698267752634 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3396535505269) ^ 1132178501756 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3396535505269) ^ 12 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_3900738859271 : Nat.Prime 3900738859271 := by
  apply lucas_primality 3900738859271 (7 : ZMod 3900738859271)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (439, 1), (80777363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (439, 1), (80777363, 1)] : List FactorBlock).map factorBlockValue).prod) = 3900738859271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_439
      · exact prime_oneHundredFiftyEightEZ_80777363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3900738859271) ^ 1950369429635 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3900738859271) ^ 780147771854 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3900738859271) ^ 354612623570 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3900738859271) ^ 8885509930 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 3900738859271) ^ 48290 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_4269575747599 : Nat.Prime 4269575747599 := by
  apply lucas_primality 4269575747599 (3 : ZMod 4269575747599)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (127, 1), (2441, 1), (327917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (127, 1), (2441, 1), (327917, 1)] : List FactorBlock).map factorBlockValue).prod) = 4269575747599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_127
      · exact prime_oneHundredFiftyEightEZ_2441
      · exact prime_oneHundredFiftyEightEZ_327917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4269575747599) ^ 2134787873799 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4269575747599) ^ 1423191915866 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4269575747599) ^ 609939392514 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4269575747599) ^ 33618706674 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4269575747599) ^ 1749109278 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 4269575747599) ^ 13020294 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_4467348527903 : Nat.Prime 4467348527903 := by
  apply lucas_primality 4467348527903 (5 : ZMod 4467348527903)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 3), (599, 1), (1697317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 3), (599, 1), (1697317, 1)] : List FactorBlock).map factorBlockValue).prod) = 4467348527903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_599
      · exact prime_oneHundredFiftyEightEZ_1697317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4467348527903) ^ 2233674263951 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 4467348527903) ^ 343642194454 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 4467348527903) ^ 7458010898 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 4467348527903) ^ 2632006 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_4995560753539 : Nat.Prime 4995560753539 := by
  apply lucas_primality 4995560753539 (2 : ZMod 4995560753539)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (3769, 1), (12994451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (3769, 1), (12994451, 1)] : List FactorBlock).map factorBlockValue).prod) = 4995560753539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_3769
      · exact prime_oneHundredFiftyEightEZ_12994451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4995560753539) ^ 2497780376769 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4995560753539) ^ 1665186917846 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4995560753539) ^ 293856514914 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4995560753539) ^ 1325434002 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4995560753539) ^ 384438 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_5544517031803 : Nat.Prime 5544517031803 := by
  apply lucas_primality 5544517031803 (2 : ZMod 5544517031803)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (44004103427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (44004103427, 1)] : List FactorBlock).map factorBlockValue).prod) = 5544517031803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_44004103427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5544517031803) ^ 2772258515901 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5544517031803) ^ 1848172343934 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5544517031803) ^ 792073861686 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5544517031803) ^ 126 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_6425666705609 : Nat.Prime 6425666705609 := by
  apply lucas_primality 6425666705609 (3 : ZMod 6425666705609)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5273, 1), (152324737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5273, 1), (152324737, 1)] : List FactorBlock).map factorBlockValue).prod) = 6425666705609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5273
      · exact prime_oneHundredFiftyEightEZ_152324737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6425666705609) ^ 3212833352804 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6425666705609) ^ 1218597896 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6425666705609) ^ 42184 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_6638594484517 : Nat.Prime 6638594484517 := by
  apply lucas_primality 6638594484517 (2 : ZMod 6638594484517)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (553216207043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (553216207043, 1)] : List FactorBlock).map factorBlockValue).prod) = 6638594484517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_553216207043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6638594484517) ^ 3319297242258 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6638594484517) ^ 2212864828172 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 6638594484517) ^ 12 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_11213427842207 : Nat.Prime 11213427842207 := by
  apply lucas_primality 11213427842207 (5 : ZMod 11213427842207)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6269, 1), (894355387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6269, 1), (894355387, 1)] : List FactorBlock).map factorBlockValue).prod) = 11213427842207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_6269
      · exact prime_oneHundredFiftyEightEZ_894355387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11213427842207) ^ 5606713921103 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11213427842207) ^ 1788710774 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 11213427842207) ^ 12538 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_12806622349891 : Nat.Prime 12806622349891 := by
  apply lucas_primality 12806622349891 (2 : ZMod 12806622349891)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (34843, 1), (12251741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (34843, 1), (12251741, 1)] : List FactorBlock).map factorBlockValue).prod) = 12806622349891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_34843
      · exact prime_oneHundredFiftyEightEZ_12251741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12806622349891) ^ 6403311174945 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12806622349891) ^ 4268874116630 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12806622349891) ^ 2561324469978 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12806622349891) ^ 367552230 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12806622349891) ^ 1045290 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_14274926905571 : Nat.Prime 14274926905571 := by
  apply lucas_primality 14274926905571 (2 : ZMod 14274926905571)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (9421, 1), (151522417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (9421, 1), (151522417, 1)] : List FactorBlock).map factorBlockValue).prod) = 14274926905571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_9421
      · exact prime_oneHundredFiftyEightEZ_151522417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14274926905571) ^ 7137463452785 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14274926905571) ^ 2854985381114 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14274926905571) ^ 1515224170 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 14274926905571) ^ 94210 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_24881408741611 : Nat.Prime 24881408741611 := by
  apply lucas_primality 24881408741611 (2 : ZMod 24881408741611)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (23, 1), (37, 1), (1993, 1), (163003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (23, 1), (37, 1), (1993, 1), (163003, 1)] : List FactorBlock).map factorBlockValue).prod) = 24881408741611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_23
      · exact prime_oneHundredFiftyEightEZ_37
      · exact prime_oneHundredFiftyEightEZ_1993
      · exact prime_oneHundredFiftyEightEZ_163003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24881408741611) ^ 12440704370805 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 24881408741611) ^ 8293802913870 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 24881408741611) ^ 4976281748322 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 24881408741611) ^ 1081800380070 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 24881408741611) ^ 672470506530 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 24881408741611) ^ 12484399770 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 24881408741611) ^ 152643870 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_27293941032767 : Nat.Prime 27293941032767 := by
  apply lucas_primality 27293941032767 (5 : ZMod 27293941032767)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (64747, 1), (210773789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (64747, 1), (210773789, 1)] : List FactorBlock).map factorBlockValue).prod) = 27293941032767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_64747
      · exact prime_oneHundredFiftyEightEZ_210773789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 27293941032767) ^ 13646970516383 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 27293941032767) ^ 421547578 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 27293941032767) ^ 129494 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_29389271132951 : Nat.Prime 29389271132951 := by
  apply lucas_primality 29389271132951 (7 : ZMod 29389271132951)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (401, 1), (3659, 1), (400601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (401, 1), (3659, 1), (400601, 1)] : List FactorBlock).map factorBlockValue).prod) = 29389271132951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_401
      · exact prime_oneHundredFiftyEightEZ_3659
      · exact prime_oneHundredFiftyEightEZ_400601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 29389271132951) ^ 14694635566475 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 29389271132951) ^ 5877854226590 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 29389271132951) ^ 73289952950 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 29389271132951) ^ 8032050050 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 29389271132951) ^ 73362950 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_30720031178467 : Nat.Prime 30720031178467 := by
  apply lucas_primality 30720031178467 (2 : ZMod 30720031178467)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (152597, 1), (4793209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (152597, 1), (4793209, 1)] : List FactorBlock).map factorBlockValue).prod) = 30720031178467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_152597
      · exact prime_oneHundredFiftyEightEZ_4793209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30720031178467) ^ 15360015589233 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 30720031178467) ^ 10240010392822 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 30720031178467) ^ 4388575882638 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 30720031178467) ^ 201314778 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 30720031178467) ^ 6409074 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_40323620939753 : Nat.Prime 40323620939753 := by
  apply lucas_primality 40323620939753 (3 : ZMod 40323620939753)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (68447, 1), (3201749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (68447, 1), (3201749, 1)] : List FactorBlock).map factorBlockValue).prod) = 40323620939753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_23
      · exact prime_oneHundredFiftyEightEZ_68447
      · exact prime_oneHundredFiftyEightEZ_3201749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40323620939753) ^ 20161810469876 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 40323620939753) ^ 1753200910424 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 40323620939753) ^ 589121816 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 40323620939753) ^ 12594248 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_77740087110409 : Nat.Prime 77740087110409 := by
  apply lucas_primality 77740087110409 (7 : ZMod 77740087110409)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (379, 1), (2848874491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (379, 1), (2848874491, 1)] : List FactorBlock).map factorBlockValue).prod) = 77740087110409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_379
      · exact prime_oneHundredFiftyEightEZ_2848874491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 77740087110409) ^ 38870043555204 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 77740087110409) ^ 25913362370136 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 77740087110409) ^ 205118963352 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 77740087110409) ^ 27288 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_82297318572269 : Nat.Prime 82297318572269 := by
  apply lucas_primality 82297318572269 (2 : ZMod 82297318572269)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167, 1), (123199578701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167, 1), (123199578701, 1)] : List FactorBlock).map factorBlockValue).prod) = 82297318572269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_167
      · exact prime_oneHundredFiftyEightEZ_123199578701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 82297318572269) ^ 41148659286134 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 82297318572269) ^ 492798314804 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 82297318572269) ^ 668 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_102460997871143 : Nat.Prime 102460997871143 := by
  apply lucas_primality 102460997871143 (5 : ZMod 102460997871143)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (877, 1), (58415620223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (877, 1), (58415620223, 1)] : List FactorBlock).map factorBlockValue).prod) = 102460997871143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_877
      · exact prime_oneHundredFiftyEightEZ_58415620223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 102460997871143) ^ 51230498935571 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 102460997871143) ^ 116831240446 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 102460997871143) ^ 1754 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_112719926577163 : Nat.Prime 112719926577163 := by
  apply lucas_primality 112719926577163 (2 : ZMod 112719926577163)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (95957, 1), (4775171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (95957, 1), (4775171, 1)] : List FactorBlock).map factorBlockValue).prod) = 112719926577163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_41
      · exact prime_oneHundredFiftyEightEZ_95957
      · exact prime_oneHundredFiftyEightEZ_4775171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 112719926577163) ^ 56359963288581 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 112719926577163) ^ 37573308859054 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 112719926577163) ^ 2749266501882 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 112719926577163) ^ 1174692066 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 112719926577163) ^ 23605422 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_202642763460707 : Nat.Prime 202642763460707 := by
  apply lucas_primality 202642763460707 (2 : ZMod 202642763460707)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (269, 1), (353, 1), (383, 1), (2785963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (269, 1), (353, 1), (383, 1), (2785963, 1)] : List FactorBlock).map factorBlockValue).prod) = 202642763460707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_269
      · exact prime_oneHundredFiftyEightEZ_353
      · exact prime_oneHundredFiftyEightEZ_383
      · exact prime_oneHundredFiftyEightEZ_2785963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 202642763460707) ^ 101321381730353 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 202642763460707) ^ 753318823274 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 202642763460707) ^ 574058820002 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 202642763460707) ^ 529093377182 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 202642763460707) ^ 72737062 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_315485472306157 : Nat.Prime 315485472306157 := by
  apply lucas_primality 315485472306157 (2 : ZMod 315485472306157)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (97, 1), (1979, 1), (2237, 1), (61223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (97, 1), (1979, 1), (2237, 1), (61223, 1)] : List FactorBlock).map factorBlockValue).prod) = 315485472306157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_97
      · exact prime_oneHundredFiftyEightEZ_1979
      · exact prime_oneHundredFiftyEightEZ_2237
      · exact prime_oneHundredFiftyEightEZ_61223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 315485472306157) ^ 157742736153078 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 315485472306157) ^ 105161824102052 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 315485472306157) ^ 3252427549548 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 315485472306157) ^ 159416610564 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 315485472306157) ^ 141030608988 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 315485472306157) ^ 5153054772 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_356344234155991 : Nat.Prime 356344234155991 := by
  apply lucas_primality 356344234155991 (3 : ZMod 356344234155991)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (43, 1), (10230957053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (43, 1), (10230957053, 1)] : List FactorBlock).map factorBlockValue).prod) = 356344234155991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_43
      · exact prime_oneHundredFiftyEightEZ_10230957053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 356344234155991) ^ 178172117077995 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 356344234155991) ^ 118781411385330 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 356344234155991) ^ 71268846831198 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 356344234155991) ^ 8287075212930 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 356344234155991) ^ 34830 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_361473313586677 : Nat.Prime 361473313586677 := by
  apply lucas_primality 361473313586677 (6 : ZMod 361473313586677)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (1667, 1), (951055351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (1667, 1), (951055351, 1)] : List FactorBlock).map factorBlockValue).prod) = 361473313586677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_1667
      · exact prime_oneHundredFiftyEightEZ_951055351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 361473313586677) ^ 180736656793338 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 361473313586677) ^ 120491104528892 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 361473313586677) ^ 19024911241404 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 361473313586677) ^ 216840620028 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 361473313586677) ^ 380076 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_433362093971603 : Nat.Prime 433362093971603 := by
  apply lucas_primality 433362093971603 (2 : ZMod 433362093971603)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6481, 1), (33433273721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6481, 1), (33433273721, 1)] : List FactorBlock).map factorBlockValue).prod) = 433362093971603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_6481
      · exact prime_oneHundredFiftyEightEZ_33433273721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 433362093971603) ^ 216681046985801 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 433362093971603) ^ 66866547442 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 433362093971603) ^ 12962 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_699823226940907 : Nat.Prime 699823226940907 := by
  apply lucas_primality 699823226940907 (2 : ZMod 699823226940907)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14503, 1), (8042281217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14503, 1), (8042281217, 1)] : List FactorBlock).map factorBlockValue).prod) = 699823226940907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_14503
      · exact prime_oneHundredFiftyEightEZ_8042281217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 699823226940907) ^ 349911613470453 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 699823226940907) ^ 233274408980302 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 699823226940907) ^ 48253687302 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 699823226940907) ^ 87018 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_899656604027777 : Nat.Prime 899656604027777 := by
  apply lucas_primality 899656604027777 (3 : ZMod 899656604027777)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (103, 1), (173, 1), (56348899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (103, 1), (173, 1), (56348899, 1)] : List FactorBlock).map factorBlockValue).prod) = 899656604027777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_103
      · exact prime_oneHundredFiftyEightEZ_173
      · exact prime_oneHundredFiftyEightEZ_56348899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 899656604027777) ^ 449828302013888 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 899656604027777) ^ 128522372003968 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 899656604027777) ^ 8734530136192 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 899656604027777) ^ 5200327190912 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 899656604027777) ^ 15965824 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_922860707248199 : Nat.Prime 922860707248199 := by
  apply lucas_primality 922860707248199 (11 : ZMod 922860707248199)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (421, 1), (1096034094119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (421, 1), (1096034094119, 1)] : List FactorBlock).map factorBlockValue).prod) = 922860707248199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_421
      · exact prime_oneHundredFiftyEightEZ_1096034094119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 922860707248199) ^ 461430353624099 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 922860707248199) ^ 2192068188238 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 922860707248199) ^ 842 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1892912833836943 : Nat.Prime 1892912833836943 := by
  apply lucas_primality 1892912833836943 (3 : ZMod 1892912833836943)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (315485472306157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (315485472306157, 1)] : List FactorBlock).map factorBlockValue).prod) = 1892912833836943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_315485472306157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1892912833836943) ^ 946456416918471 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1892912833836943) ^ 630970944612314 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 1892912833836943) ^ 6 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2057795156113379 : Nat.Prime 2057795156113379 := by
  apply lucas_primality 2057795156113379 (2 : ZMod 2057795156113379)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (109, 1), (29590681259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (109, 1), (29590681259, 1)] : List FactorBlock).map factorBlockValue).prod) = 2057795156113379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_29
      · exact prime_oneHundredFiftyEightEZ_109
      · exact prime_oneHundredFiftyEightEZ_29590681259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2057795156113379) ^ 1028897578056689 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2057795156113379) ^ 187072286919398 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2057795156113379) ^ 70958453659082 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2057795156113379) ^ 18878854643242 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2057795156113379) ^ 69542 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2268260700492637 : Nat.Prime 2268260700492637 := by
  apply lucas_primality 2268260700492637 (2 : ZMod 2268260700492637)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29, 1), (2172663506219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29, 1), (2172663506219, 1)] : List FactorBlock).map factorBlockValue).prod) = 2268260700492637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_29
      · exact prime_oneHundredFiftyEightEZ_2172663506219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2268260700492637) ^ 1134130350246318 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2268260700492637) ^ 756086900164212 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2268260700492637) ^ 78215886223884 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2268260700492637) ^ 1044 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2458366639213759 : Nat.Prime 2458366639213759 := by
  apply lucas_primality 2458366639213759 (3 : ZMod 2458366639213759)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (251, 1), (1303, 1), (13766891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (251, 1), (1303, 1), (13766891, 1)] : List FactorBlock).map factorBlockValue).prod) = 2458366639213759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_251
      · exact prime_oneHundredFiftyEightEZ_1303
      · exact prime_oneHundredFiftyEightEZ_13766891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2458366639213759) ^ 1229183319606879 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2458366639213759) ^ 819455546404586 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2458366639213759) ^ 351195234173394 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2458366639213759) ^ 189105126093366 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2458366639213759) ^ 9794289399258 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2458366639213759) ^ 1886697343986 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2458366639213759) ^ 178570938 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_3060006329088659 : Nat.Prime 3060006329088659 := by
  apply lucas_primality 3060006329088659 (2 : ZMod 3060006329088659)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (827, 1), (87323, 1), (218417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (827, 1), (87323, 1), (218417, 1)] : List FactorBlock).map factorBlockValue).prod) = 3060006329088659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_97
      · exact prime_oneHundredFiftyEightEZ_827
      · exact prime_oneHundredFiftyEightEZ_87323
      · exact prime_oneHundredFiftyEightEZ_218417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3060006329088659) ^ 1530003164544329 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3060006329088659) ^ 31546457000914 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3060006329088659) ^ 3700128572054 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3060006329088659) ^ 35042386646 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3060006329088659) ^ 14009927474 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_3614135632786271 : Nat.Prime 3614135632786271 := by
  apply lucas_primality 3614135632786271 (13 : ZMod 3614135632786271)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (97, 1), (1031, 1), (212581333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (97, 1), (1031, 1), (212581333, 1)] : List FactorBlock).map factorBlockValue).prod) = 3614135632786271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_97
      · exact prime_oneHundredFiftyEightEZ_1031
      · exact prime_oneHundredFiftyEightEZ_212581333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3614135632786271) ^ 1807067816393135 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3614135632786271) ^ 722827126557254 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3614135632786271) ^ 212596213693310 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3614135632786271) ^ 37259130234910 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3614135632786271) ^ 3505466181170 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 3614135632786271) ^ 17001190 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_4708167619799101 : Nat.Prime 4708167619799101 := by
  apply lucas_primality 4708167619799101 (6 : ZMod 4708167619799101)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (19, 1), (499, 1), (743, 1), (2227859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (19, 1), (499, 1), (743, 1), (2227859, 1)] : List FactorBlock).map factorBlockValue).prod) = 4708167619799101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_499
      · exact prime_oneHundredFiftyEightEZ_743
      · exact prime_oneHundredFiftyEightEZ_2227859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4708167619799101) ^ 2354083809899550 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4708167619799101) ^ 1569389206599700 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4708167619799101) ^ 941633523959820 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4708167619799101) ^ 247798295778900 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4708167619799101) ^ 9435205650900 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4708167619799101) ^ 6336699353700 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 4708167619799101) ^ 2113314900 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_4958180680080557 : Nat.Prime 4958180680080557 := by
  apply lucas_primality 4958180680080557 (2 : ZMod 4958180680080557)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89, 1), (34843, 1), (399720857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89, 1), (34843, 1), (399720857, 1)] : List FactorBlock).map factorBlockValue).prod) = 4958180680080557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_89
      · exact prime_oneHundredFiftyEightEZ_34843
      · exact prime_oneHundredFiftyEightEZ_399720857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4958180680080557) ^ 2479090340040278 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4958180680080557) ^ 55709895281804 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4958180680080557) ^ 142300625092 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4958180680080557) ^ 12404108 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_5911496190063901 : Nat.Prime 5911496190063901 := by
  apply lucas_primality 5911496190063901 (2 : ZMod 5911496190063901)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (29, 1), (75498035633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (29, 1), (75498035633, 1)] : List FactorBlock).map factorBlockValue).prod) = 5911496190063901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_29
      · exact prime_oneHundredFiftyEightEZ_75498035633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5911496190063901) ^ 2955748095031950 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5911496190063901) ^ 1970498730021300 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5911496190063901) ^ 1182299238012780 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5911496190063901) ^ 203844696209100 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 5911496190063901) ^ 78300 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_5926587081499991 : Nat.Prime 5926587081499991 := by
  apply lucas_primality 5926587081499991 (7 : ZMod 5926587081499991)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (83, 1), (8243, 1), (27017, 1), (32063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (83, 1), (8243, 1), (27017, 1), (32063, 1)] : List FactorBlock).map factorBlockValue).prod) = 5926587081499991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_83
      · exact prime_oneHundredFiftyEightEZ_8243
      · exact prime_oneHundredFiftyEightEZ_27017
      · exact prime_oneHundredFiftyEightEZ_32063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5926587081499991) ^ 2963293540749995 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5926587081499991) ^ 1185317416299998 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5926587081499991) ^ 71404663632530 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5926587081499991) ^ 718984238930 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5926587081499991) ^ 219365106470 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 5926587081499991) ^ 184841938730 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_6507933775024807 : Nat.Prime 6507933775024807 := by
  apply lucas_primality 6507933775024807 (3 : ZMod 6507933775024807)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (29, 1), (16649, 1), (249610709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (29, 1), (16649, 1), (249610709, 1)] : List FactorBlock).map factorBlockValue).prod) = 6507933775024807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_29
      · exact prime_oneHundredFiftyEightEZ_16649
      · exact prime_oneHundredFiftyEightEZ_249610709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6507933775024807) ^ 3253966887512403 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6507933775024807) ^ 2169311258341602 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6507933775024807) ^ 224411509483614 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6507933775024807) ^ 390890370294 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 6507933775024807) ^ 26072334 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_8278591165857829 : Nat.Prime 8278591165857829 := by
  apply lucas_primality 8278591165857829 (2 : ZMod 8278591165857829)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5828441, 1), (13151651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5828441, 1), (13151651, 1)] : List FactorBlock).map factorBlockValue).prod) = 8278591165857829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5828441
      · exact prime_oneHundredFiftyEightEZ_13151651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8278591165857829) ^ 4139295582928914 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8278591165857829) ^ 2759530388619276 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8278591165857829) ^ 1420378308 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8278591165857829) ^ 629471628 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_10985410087566511 : Nat.Prime 10985410087566511 := by
  apply lucas_primality 10985410087566511 (6 : ZMod 10985410087566511)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (2038019, 1), (7811941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (2038019, 1), (7811941, 1)] : List FactorBlock).map factorBlockValue).prod) = 10985410087566511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_23
      · exact prime_oneHundredFiftyEightEZ_2038019
      · exact prime_oneHundredFiftyEightEZ_7811941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10985410087566511) ^ 5492705043783255 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 10985410087566511) ^ 3661803362522170 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 10985410087566511) ^ 2197082017513302 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 10985410087566511) ^ 477626525546370 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 10985410087566511) ^ 5390239290 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 10985410087566511) ^ 1406233110 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_14305460572214711 : Nat.Prime 14305460572214711 := by
  apply lucas_primality 14305460572214711 (7 : ZMod 14305460572214711)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4523, 1), (23819, 1), (13278583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4523, 1), (23819, 1), (13278583, 1)] : List FactorBlock).map factorBlockValue).prod) = 14305460572214711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_4523
      · exact prime_oneHundredFiftyEightEZ_23819
      · exact prime_oneHundredFiftyEightEZ_13278583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14305460572214711) ^ 7152730286107355 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14305460572214711) ^ 2861092114442942 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14305460572214711) ^ 3162825684770 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14305460572214711) ^ 600590309090 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 14305460572214711) ^ 1077333370 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_15230019096283987 : Nat.Prime 15230019096283987 := by
  apply lucas_primality 15230019096283987 (2 : ZMod 15230019096283987)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (27293941032767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (27293941032767, 1)] : List FactorBlock).map factorBlockValue).prod) = 15230019096283987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_31
      · exact prime_oneHundredFiftyEightEZ_27293941032767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15230019096283987) ^ 7615009548141993 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15230019096283987) ^ 5076673032094662 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15230019096283987) ^ 491290938589806 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15230019096283987) ^ 558 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_15810324432082003 : Nat.Prime 15810324432082003 := by
  apply lucas_primality 15810324432082003 (2 : ZMod 15810324432082003)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (131, 1), (4793, 1), (37808359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (131, 1), (4793, 1), (37808359, 1)] : List FactorBlock).map factorBlockValue).prod) = 15810324432082003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_37
      · exact prime_oneHundredFiftyEightEZ_131
      · exact prime_oneHundredFiftyEightEZ_4793
      · exact prime_oneHundredFiftyEightEZ_37808359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15810324432082003) ^ 7905162216041001 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15810324432082003) ^ 5270108144027334 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15810324432082003) ^ 427306065731946 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15810324432082003) ^ 120689499481542 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15810324432082003) ^ 3298628089314 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 15810324432082003) ^ 418170078 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_16499536835262449 : Nat.Prime 16499536835262449 := by
  apply lucas_primality 16499536835262449 (3 : ZMod 16499536835262449)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 2), (41, 1), (207865561823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 2), (41, 1), (207865561823, 1)] : List FactorBlock).map factorBlockValue).prod) = 16499536835262449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_41
      · exact prime_oneHundredFiftyEightEZ_207865561823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 16499536835262449) ^ 8249768417631224 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 16499536835262449) ^ 1499957894114768 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 16499536835262449) ^ 402427727689328 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 16499536835262449) ^ 79376 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_20463573774419233 : Nat.Prime 20463573774419233 := by
  apply lucas_primality 20463573774419233 (5 : ZMod 20463573774419233)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (127447, 1), (1672555861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (127447, 1), (1672555861, 1)] : List FactorBlock).map factorBlockValue).prod) = 20463573774419233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_127447
      · exact prime_oneHundredFiftyEightEZ_1672555861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20463573774419233) ^ 10231786887209616 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20463573774419233) ^ 6821191258139744 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20463573774419233) ^ 160565362656 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20463573774419233) ^ 12234912 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_23461052606333801 : Nat.Prime 23461052606333801 := by
  apply lucas_primality 23461052606333801 (3 : ZMod 23461052606333801)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7517, 1), (62927, 1), (247991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7517, 1), (62927, 1), (247991, 1)] : List FactorBlock).map factorBlockValue).prod) = 23461052606333801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7517
      · exact prime_oneHundredFiftyEightEZ_62927
      · exact prime_oneHundredFiftyEightEZ_247991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23461052606333801) ^ 11730526303166900 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 23461052606333801) ^ 4692210521266760 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 23461052606333801) ^ 3121065931400 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 23461052606333801) ^ 372829669400 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 23461052606333801) ^ 94604451800 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_24720344221351501 : Nat.Prime 24720344221351501 := by
  apply lucas_primality 24720344221351501 (13 : ZMod 24720344221351501)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 6), (5, 3), (431, 1), (457, 1), (344321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 6), (5, 3), (431, 1), (457, 1), (344321, 1)] : List FactorBlock).map factorBlockValue).prod) = 24720344221351501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_431
      · exact prime_oneHundredFiftyEightEZ_457
      · exact prime_oneHundredFiftyEightEZ_344321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 24720344221351501) ^ 12360172110675750 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 24720344221351501) ^ 8240114740450500 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 24720344221351501) ^ 4944068844270300 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 24720344221351501) ^ 57355787056500 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 24720344221351501) ^ 54092656939500 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 24720344221351501) ^ 71794471500 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_76894399445572439 : Nat.Prime 76894399445572439 := by
  apply lucas_primality 76894399445572439 (11 : ZMod 76894399445572439)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (9403, 1), (240518981569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (9403, 1), (240518981569, 1)] : List FactorBlock).map factorBlockValue).prod) = 76894399445572439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_9403
      · exact prime_oneHundredFiftyEightEZ_240518981569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 76894399445572439) ^ 38447199722786219 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 76894399445572439) ^ 4523199967386614 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 76894399445572439) ^ 8177645373346 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 76894399445572439) ^ 319702 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_188834557979440301 : Nat.Prime 188834557979440301 := by
  apply lucas_primality 188834557979440301 (2 : ZMod 188834557979440301)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (227, 1), (9157, 1), (908452877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (227, 1), (9157, 1), (908452877, 1)] : List FactorBlock).map factorBlockValue).prod) = 188834557979440301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_227
      · exact prime_oneHundredFiftyEightEZ_9157
      · exact prime_oneHundredFiftyEightEZ_908452877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 188834557979440301) ^ 94417278989720150 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 188834557979440301) ^ 37766911595888060 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 188834557979440301) ^ 831870299468900 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 188834557979440301) ^ 20621880307900 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 188834557979440301) ^ 207863900 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_242474527855275983 : Nat.Prime 242474527855275983 := by
  apply lucas_primality 242474527855275983 (5 : ZMod 242474527855275983)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3467, 1), (4995560753539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3467, 1), (4995560753539, 1)] : List FactorBlock).map factorBlockValue).prod) = 242474527855275983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_3467
      · exact prime_oneHundredFiftyEightEZ_4995560753539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 242474527855275983) ^ 121237263927637991 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 242474527855275983) ^ 34639218265039426 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 242474527855275983) ^ 69937850549546 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 242474527855275983) ^ 48538 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_490157813223534013 : Nat.Prime 490157813223534013 := by
  apply lucas_primality 490157813223534013 (5 : ZMod 490157813223534013)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (113, 1), (361473313586677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (113, 1), (361473313586677, 1)] : List FactorBlock).map factorBlockValue).prod) = 490157813223534013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_113
      · exact prime_oneHundredFiftyEightEZ_361473313586677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 490157813223534013) ^ 245078906611767006 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 490157813223534013) ^ 163385937741178004 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 490157813223534013) ^ 4337679763040124 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 490157813223534013) ^ 1356 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_565577636252618071 : Nat.Prime 565577636252618071 := by
  apply lucas_primality 565577636252618071 (6 : ZMod 565577636252618071)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (73, 1), (6744239, 1), (12764209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (73, 1), (6744239, 1), (12764209, 1)] : List FactorBlock).map factorBlockValue).prod) = 565577636252618071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_73
      · exact prime_oneHundredFiftyEightEZ_6744239
      · exact prime_oneHundredFiftyEightEZ_12764209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 565577636252618071) ^ 282788818126309035 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 565577636252618071) ^ 188525878750872690 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 565577636252618071) ^ 113115527250523614 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 565577636252618071) ^ 7747638852775590 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 565577636252618071) ^ 83860853130 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 565577636252618071) ^ 44309650230 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_600422478739871407 : Nat.Prime 600422478739871407 := by
  apply lucas_primality 600422478739871407 (3 : ZMod 600422478739871407)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (233, 1), (1787, 1), (240339536431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (233, 1), (1787, 1), (240339536431, 1)] : List FactorBlock).map factorBlockValue).prod) = 600422478739871407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_233
      · exact prime_oneHundredFiftyEightEZ_1787
      · exact prime_oneHundredFiftyEightEZ_240339536431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 600422478739871407) ^ 300211239369935703 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 600422478739871407) ^ 200140826246623802 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 600422478739871407) ^ 2576920509613182 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 600422478739871407) ^ 335994671930538 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 600422478739871407) ^ 2498226 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_720971914273780963 : Nat.Prime 720971914273780963 := by
  apply lucas_primality 720971914273780963 (2 : ZMod 720971914273780963)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (2939, 1), (3145025406661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (2939, 1), (3145025406661, 1)] : List FactorBlock).map factorBlockValue).prod) = 720971914273780963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_2939
      · exact prime_oneHundredFiftyEightEZ_3145025406661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 720971914273780963) ^ 360485957136890481 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 720971914273780963) ^ 240323971424593654 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 720971914273780963) ^ 55459378021060074 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 720971914273780963) ^ 245311981719558 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 720971914273780963) ^ 229242 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_829098482468746393 : Nat.Prime 829098482468746393 := by
  apply lucas_primality 829098482468746393 (10 : ZMod 829098482468746393)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (101, 1), (487, 1), (57529, 1), (581351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (101, 1), (487, 1), (57529, 1), (581351, 1)] : List FactorBlock).map factorBlockValue).prod) = 829098482468746393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_101
      · exact prime_oneHundredFiftyEightEZ_487
      · exact prime_oneHundredFiftyEightEZ_57529
      · exact prime_oneHundredFiftyEightEZ_581351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 829098482468746393) ^ 414549241234373196 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 829098482468746393) ^ 276366160822915464 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 829098482468746393) ^ 118442640352678056 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 829098482468746393) ^ 8208895866027192 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 829098482468746393) ^ 1702460949627816 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 829098482468746393) ^ 14411835465048 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 829098482468746393) ^ 1426158177192 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_876524909588327081 : Nat.Prime 876524909588327081 := by
  apply lucas_primality 876524909588327081 (3 : ZMod 876524909588327081)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (44452963, 1), (492950779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (44452963, 1), (492950779, 1)] : List FactorBlock).map factorBlockValue).prod) = 876524909588327081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_44452963
      · exact prime_oneHundredFiftyEightEZ_492950779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 876524909588327081) ^ 438262454794163540 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 876524909588327081) ^ 175304981917665416 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 876524909588327081) ^ 19718031160 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 876524909588327081) ^ 1778118520 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1186246104571394117 : Nat.Prime 1186246104571394117 := by
  apply lucas_primality 1186246104571394117 (2 : ZMod 1186246104571394117)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (499, 1), (11213427842207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (499, 1), (11213427842207, 1)] : List FactorBlock).map factorBlockValue).prod) = 1186246104571394117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_53
      · exact prime_oneHundredFiftyEightEZ_499
      · exact prime_oneHundredFiftyEightEZ_11213427842207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1186246104571394117) ^ 593123052285697058 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1186246104571394117) ^ 22382001973045172 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1186246104571394117) ^ 2377246702547884 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1186246104571394117) ^ 105788 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1239142961267146907 : Nat.Prime 1239142961267146907 := by
  apply lucas_primality 1239142961267146907 (2 : ZMod 1239142961267146907)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (163, 1), (563, 1), (151429, 1), (1087433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (163, 1), (563, 1), (151429, 1), (1087433, 1)] : List FactorBlock).map factorBlockValue).prod) = 1239142961267146907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_41
      · exact prime_oneHundredFiftyEightEZ_163
      · exact prime_oneHundredFiftyEightEZ_563
      · exact prime_oneHundredFiftyEightEZ_151429
      · exact prime_oneHundredFiftyEightEZ_1087433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1239142961267146907) ^ 619571480633573453 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1239142961267146907) ^ 30222999055296266 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1239142961267146907) ^ 7602104056853662 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1239142961267146907) ^ 2200964407224062 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1239142961267146907) ^ 8182996396114 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1239142961267146907) ^ 1139512007882 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1446237963529957321 : Nat.Prime 1446237963529957321 := by
  apply lucas_primality 1446237963529957321 (14 : ZMod 1446237963529957321)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (19, 1), (838993, 1), (756043133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (19, 1), (838993, 1), (756043133, 1)] : List FactorBlock).map factorBlockValue).prod) = 1446237963529957321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_838993
      · exact prime_oneHundredFiftyEightEZ_756043133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1446237963529957321) ^ 723118981764978660 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 1446237963529957321) ^ 482079321176652440 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 1446237963529957321) ^ 289247592705991464 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 1446237963529957321) ^ 76117787554208280 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 1446237963529957321) ^ 1723778343240 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 1446237963529957321) ^ 1912904040 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1515889605573545339 : Nat.Prime 1515889605573545339 := by
  apply lucas_primality 1515889605573545339 (2 : ZMod 1515889605573545339)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (15217, 1), (559652608213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (15217, 1), (559652608213, 1)] : List FactorBlock).map factorBlockValue).prod) = 1515889605573545339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_89
      · exact prime_oneHundredFiftyEightEZ_15217
      · exact prime_oneHundredFiftyEightEZ_559652608213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1515889605573545339) ^ 757944802786772669 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1515889605573545339) ^ 17032467478354442 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1515889605573545339) ^ 99618164261914 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1515889605573545339) ^ 2708626 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_101
      · exact prime_oneHundredFiftyEightEZ_191
      · exact prime_oneHundredFiftyEightEZ_48017
      · exact prime_oneHundredFiftyEightEZ_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2965548649312744169 : Nat.Prime 2965548649312744169 := by
  apply lucas_primality 2965548649312744169 (6 : ZMod 2965548649312744169)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (29, 1), (53, 2), (1223, 1), (218871871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (29, 1), (53, 2), (1223, 1), (218871871, 1)] : List FactorBlock).map factorBlockValue).prod) = 2965548649312744169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_29
      · exact prime_oneHundredFiftyEightEZ_53
      · exact prime_oneHundredFiftyEightEZ_1223
      · exact prime_oneHundredFiftyEightEZ_218871871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2965548649312744169) ^ 1482774324656372084 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2965548649312744169) ^ 174444038194867304 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2965548649312744169) ^ 102260298252163592 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2965548649312744169) ^ 55953748100240456 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2965548649312744169) ^ 2424814921760216 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 2965548649312744169) ^ 13549245208 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_3509624183824913131 : Nat.Prime 3509624183824913131 := by
  apply lucas_primality 3509624183824913131 (2 : ZMod 3509624183824913131)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (93581, 1), (138902213999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (93581, 1), (138902213999, 1)] : List FactorBlock).map factorBlockValue).prod) = 3509624183824913131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_93581
      · exact prime_oneHundredFiftyEightEZ_138902213999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3509624183824913131) ^ 1754812091912456565 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3509624183824913131) ^ 1169874727941637710 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3509624183824913131) ^ 701924836764982626 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3509624183824913131) ^ 37503597779730 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 3509624183824913131) ^ 25266870 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_6830496520238248063 : Nat.Prime 6830496520238248063 := by
  apply lucas_primality 6830496520238248063 (5 : ZMod 6830496520238248063)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1223, 1), (1621, 1), (10979, 1), (52303261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1223, 1), (1621, 1), (10979, 1), (52303261, 1)] : List FactorBlock).map factorBlockValue).prod) = 6830496520238248063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_1223
      · exact prime_oneHundredFiftyEightEZ_1621
      · exact prime_oneHundredFiftyEightEZ_10979
      · exact prime_oneHundredFiftyEightEZ_52303261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6830496520238248063) ^ 3415248260119124031 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6830496520238248063) ^ 2276832173412749354 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6830496520238248063) ^ 5585033949499794 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6830496520238248063) ^ 4213754793484422 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6830496520238248063) ^ 622141954662378 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 6830496520238248063) ^ 130594085142 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_11145676808622130673 : Nat.Prime 11145676808622130673 := by
  apply lucas_primality 11145676808622130673 (3 : ZMod 11145676808622130673)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (27997, 1), (24881408741611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (27997, 1), (24881408741611, 1)] : List FactorBlock).map factorBlockValue).prod) = 11145676808622130673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_27997
      · exact prime_oneHundredFiftyEightEZ_24881408741611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11145676808622130673) ^ 5572838404311065336 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 11145676808622130673) ^ 398102539865776 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 11145676808622130673) ^ 447952 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_15205179346458550387 : Nat.Prime 15205179346458550387 := by
  apply lucas_primality 15205179346458550387 (3 : ZMod 15205179346458550387)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (197, 1), (345271, 1), (5322503159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (197, 1), (345271, 1), (5322503159, 1)] : List FactorBlock).map factorBlockValue).prod) = 15205179346458550387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_197
      · exact prime_oneHundredFiftyEightEZ_345271
      · exact prime_oneHundredFiftyEightEZ_5322503159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15205179346458550387) ^ 7602589673229275193 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15205179346458550387) ^ 5068393115486183462 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15205179346458550387) ^ 2172168478065507198 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15205179346458550387) ^ 77183651504865738 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15205179346458550387) ^ 44038391137566 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 15205179346458550387) ^ 2856772254 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_17853868007922800033 : Nat.Prime 17853868007922800033 := by
  apply lucas_primality 17853868007922800033 (3 : ZMod 17853868007922800033)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (53, 1), (691, 1), (590839, 1), (25784533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (53, 1), (691, 1), (590839, 1), (25784533, 1)] : List FactorBlock).map factorBlockValue).prod) = 17853868007922800033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_53
      · exact prime_oneHundredFiftyEightEZ_691
      · exact prime_oneHundredFiftyEightEZ_590839
      · exact prime_oneHundredFiftyEightEZ_25784533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17853868007922800033) ^ 8926934003961400016 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 17853868007922800033) ^ 336865434111750944 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 17853868007922800033) ^ 25837725047645152 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 17853868007922800033) ^ 30217822465888 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 17853868007922800033) ^ 692425494304 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_20819438555436765697 : Nat.Prime 20819438555436765697 := by
  apply lucas_primality 20819438555436765697 (5 : ZMod 20819438555436765697)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (17, 1), (151, 1), (953, 1), (5540628461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (17, 1), (151, 1), (953, 1), (5540628461, 1)] : List FactorBlock).map factorBlockValue).prod) = 20819438555436765697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_151
      · exact prime_oneHundredFiftyEightEZ_953
      · exact prime_oneHundredFiftyEightEZ_5540628461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 20819438555436765697) ^ 10409719277718382848 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20819438555436765697) ^ 6939812851812255232 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20819438555436765697) ^ 1224672856202162688 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20819438555436765697) ^ 137877076526071296 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20819438555436765697) ^ 21846210446418432 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 20819438555436765697) ^ 3757595136 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_46461771702976334933 : Nat.Prime 46461771702976334933 := by
  apply lucas_primality 46461771702976334933 (2 : ZMod 46461771702976334933)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (457, 1), (1299821, 1), (19554018689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (457, 1), (1299821, 1), (19554018689, 1)] : List FactorBlock).map factorBlockValue).prod) = 46461771702976334933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_457
      · exact prime_oneHundredFiftyEightEZ_1299821
      · exact prime_oneHundredFiftyEightEZ_19554018689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46461771702976334933) ^ 23230885851488167466 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 46461771702976334933) ^ 101666896505418676 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 46461771702976334933) ^ 35744746163492 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 46461771702976334933) ^ 2376072788 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_66069472740616929607 : Nat.Prime 66069472740616929607 := by
  apply lucas_primality 66069472740616929607 (5 : ZMod 66069472740616929607)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (572183, 1), (1749532260277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (572183, 1), (1749532260277, 1)] : List FactorBlock).map factorBlockValue).prod) = 66069472740616929607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_572183
      · exact prime_oneHundredFiftyEightEZ_1749532260277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 66069472740616929607) ^ 33034736370308464803 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 66069472740616929607) ^ 22023157580205643202 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 66069472740616929607) ^ 6006315703692448146 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 66069472740616929607) ^ 115469129178282 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 66069472740616929607) ^ 37764078 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_68486595296926186613 : Nat.Prime 68486595296926186613 := by
  apply lucas_primality 68486595296926186613 (2 : ZMod 68486595296926186613)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (336939373, 1), (50815221361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (336939373, 1), (50815221361, 1)] : List FactorBlock).map factorBlockValue).prod) = 68486595296926186613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_336939373
      · exact prime_oneHundredFiftyEightEZ_50815221361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68486595296926186613) ^ 34243297648463093306 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 68486595296926186613) ^ 203260885444 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 68486595296926186613) ^ 1347757492 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_78835699087393023337 : Nat.Prime 78835699087393023337 := by
  apply lucas_primality 78835699087393023337 (5 : ZMod 78835699087393023337)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (59, 1), (269, 1), (7207, 1), (2610719317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (59, 1), (269, 1), (7207, 1), (2610719317, 1)] : List FactorBlock).map factorBlockValue).prod) = 78835699087393023337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_59
      · exact prime_oneHundredFiftyEightEZ_269
      · exact prime_oneHundredFiftyEightEZ_7207
      · exact prime_oneHundredFiftyEightEZ_2610719317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 78835699087393023337) ^ 39417849543696511668 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 78835699087393023337) ^ 26278566362464341112 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 78835699087393023337) ^ 7166881735217547576 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 78835699087393023337) ^ 1336198289616830904 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 78835699087393023337) ^ 293069513336033544 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 78835699087393023337) ^ 10938767737948248 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 78835699087393023337) ^ 30196926408 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_79298919226740479153 : Nat.Prime 79298919226740479153 := by
  apply lucas_primality 79298919226740479153 (3 : ZMod 79298919226740479153)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43969, 1), (112719926577163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43969, 1), (112719926577163, 1)] : List FactorBlock).map factorBlockValue).prod) = 79298919226740479153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_43969
      · exact prime_oneHundredFiftyEightEZ_112719926577163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 79298919226740479153) ^ 39649459613370239576 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 79298919226740479153) ^ 1803518825234608 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 79298919226740479153) ^ 703504 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_89500863873037785013 : Nat.Prime 89500863873037785013 := by
  apply lucas_primality 89500863873037785013 (2 : ZMod 89500863873037785013)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (463, 1), (105229, 1), (1308409489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (463, 1), (105229, 1), (1308409489, 1)] : List FactorBlock).map factorBlockValue).prod) = 89500863873037785013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_463
      · exact prime_oneHundredFiftyEightEZ_105229
      · exact prime_oneHundredFiftyEightEZ_1308409489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89500863873037785013) ^ 44750431936518892506 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 89500863873037785013) ^ 29833621291012595004 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 89500863873037785013) ^ 6884681836387521924 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 89500863873037785013) ^ 193306401453645324 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 89500863873037785013) ^ 850534205143428 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 89500863873037785013) ^ 68404321908 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_181658844776221569563 : Nat.Prime 181658844776221569563 := by
  apply lucas_primality 181658844776221569563 (2 : ZMod 181658844776221569563)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (37, 1), (188834557979440301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (37, 1), (188834557979440301, 1)] : List FactorBlock).map factorBlockValue).prod) = 181658844776221569563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_37
      · exact prime_oneHundredFiftyEightEZ_188834557979440301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 181658844776221569563) ^ 90829422388110784781 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 181658844776221569563) ^ 13973757290478582274 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 181658844776221569563) ^ 4909698507465447826 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 181658844776221569563) ^ 962 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_183864016257390138479 : Nat.Prime 183864016257390138479 := by
  apply lucas_primality 183864016257390138479 (23 : ZMod 183864016257390138479)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (2965548649312744169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (2965548649312744169, 1)] : List FactorBlock).map factorBlockValue).prod) = 183864016257390138479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_31
      · exact prime_oneHundredFiftyEightEZ_2965548649312744169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 183864016257390138479) ^ 91932008128695069239 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (23 : ZMod 183864016257390138479) ^ 5931097298625488338 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (23 : ZMod 183864016257390138479) ^ 62 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_206406822195422576359 : Nat.Prime 206406822195422576359 := by
  apply lucas_primality 206406822195422576359 (3 : ZMod 206406822195422576359)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (1186246104571394117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (1186246104571394117, 1)] : List FactorBlock).map factorBlockValue).prod) = 206406822195422576359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_29
      · exact prime_oneHundredFiftyEightEZ_1186246104571394117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 206406822195422576359) ^ 103203411097711288179 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 206406822195422576359) ^ 68802274065140858786 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 206406822195422576359) ^ 7117476627428364702 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 206406822195422576359) ^ 174 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_399105566782993713271 : Nat.Prime 399105566782993713271 := by
  apply lucas_primality 399105566782993713271 (6 : ZMod 399105566782993713271)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (3709, 1), (3803, 1), (98911, 1), (501863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (3709, 1), (3803, 1), (98911, 1), (501863, 1)] : List FactorBlock).map factorBlockValue).prod) = 399105566782993713271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_3709
      · exact prime_oneHundredFiftyEightEZ_3803
      · exact prime_oneHundredFiftyEightEZ_98911
      · exact prime_oneHundredFiftyEightEZ_501863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 399105566782993713271) ^ 199552783391496856635 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 399105566782993713271) ^ 133035188927664571090 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 399105566782993713271) ^ 79821113356598742654 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 399105566782993713271) ^ 21005556146473353330 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 399105566782993713271) ^ 107604628412778030 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 399105566782993713271) ^ 104944929472257090 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 399105566782993713271) ^ 4034996782794570 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 399105566782993713271) ^ 795248039371290 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_624157901282839317689 : Nat.Prime 624157901282839317689 := by
  apply lucas_primality 624157901282839317689 (3 : ZMod 624157901282839317689)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11145676808622130673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11145676808622130673, 1)] : List FactorBlock).map factorBlockValue).prod) = 624157901282839317689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_11145676808622130673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 624157901282839317689) ^ 312078950641419658844 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 624157901282839317689) ^ 89165414468977045384 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 624157901282839317689) ^ 56 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_687938836688752114537 : Nat.Prime 687938836688752114537 := by
  apply lucas_primality 687938836688752114537 (15 : ZMod 687938836688752114537)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (37, 1), (15810324432082003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (37, 1), (15810324432082003, 1)] : List FactorBlock).map factorBlockValue).prod) = 687938836688752114537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_37
      · exact prime_oneHundredFiftyEightEZ_15810324432082003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 687938836688752114537) ^ 343969418344376057268 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (15 : ZMod 687938836688752114537) ^ 229312945562917371512 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (15 : ZMod 687938836688752114537) ^ 98276976669821730648 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (15 : ZMod 687938836688752114537) ^ 18592941532128435528 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (15 : ZMod 687938836688752114537) ^ 43512 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1070709075317951374043 : Nat.Prime 1070709075317951374043 := by
  apply lucas_primality 1070709075317951374043 (2 : ZMod 1070709075317951374043)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (877, 1), (5926587081499991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (877, 1), (5926587081499991, 1)] : List FactorBlock).map factorBlockValue).prod) = 1070709075317951374043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_103
      · exact prime_oneHundredFiftyEightEZ_877
      · exact prime_oneHundredFiftyEightEZ_5926587081499991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1070709075317951374043) ^ 535354537658975687021 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1070709075317951374043) ^ 10395233740950984214 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1070709075317951374043) ^ 1220876938788998146 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1070709075317951374043) ^ 180662 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1383560558015636680387 : Nat.Prime 1383560558015636680387 := by
  apply lucas_primality 1383560558015636680387 (2 : ZMod 1383560558015636680387)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (59, 1), (89, 1), (157, 1), (211, 1), (5118268117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (59, 1), (89, 1), (157, 1), (211, 1), (5118268117, 1)] : List FactorBlock).map factorBlockValue).prod) = 1383560558015636680387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_37
      · exact prime_oneHundredFiftyEightEZ_59
      · exact prime_oneHundredFiftyEightEZ_89
      · exact prime_oneHundredFiftyEightEZ_157
      · exact prime_oneHundredFiftyEightEZ_211
      · exact prime_oneHundredFiftyEightEZ_5118268117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1383560558015636680387) ^ 691780279007818340193 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383560558015636680387) ^ 461186852671878893462 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383560558015636680387) ^ 197651508287948097198 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383560558015636680387) ^ 37393528595017207578 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383560558015636680387) ^ 23450178949417570854 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383560558015636680387) ^ 15545624247366704274 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383560558015636680387) ^ 8812487630672845098 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383560558015636680387) ^ 6557159042728135926 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1383560558015636680387) ^ 270318108858 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1585978384534809583061 : Nat.Prime 1585978384534809583061 := by
  apply lucas_primality 1585978384534809583061 (2 : ZMod 1585978384534809583061)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (79298919226740479153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (79298919226740479153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1585978384534809583061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_79298919226740479153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1585978384534809583061) ^ 792989192267404791530 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1585978384534809583061) ^ 317195676906961916612 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1585978384534809583061) ^ 20 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2640444585235319401753 : Nat.Prime 2640444585235319401753 := by
  apply lucas_primality 2640444585235319401753 (10 : ZMod 2640444585235319401753)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (463, 1), (11018303, 1), (21566025457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (463, 1), (11018303, 1), (21566025457, 1)] : List FactorBlock).map factorBlockValue).prod) = 2640444585235319401753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_463
      · exact prime_oneHundredFiftyEightEZ_11018303
      · exact prime_oneHundredFiftyEightEZ_21566025457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2640444585235319401753) ^ 1320222292617659700876 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2640444585235319401753) ^ 880148195078439800584 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2640444585235319401753) ^ 5702904071782547304 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2640444585235319401753) ^ 239641674878184 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 2640444585235319401753) ^ 122435382936 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2740587386528899990889 : Nat.Prime 2740587386528899990889 := by
  apply lucas_primality 2740587386528899990889 (3 : ZMod 2740587386528899990889)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (896647, 1), (29389271132951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (896647, 1), (29389271132951, 1)] : List FactorBlock).map factorBlockValue).prod) = 2740587386528899990889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_896647
      · exact prime_oneHundredFiftyEightEZ_29389271132951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2740587386528899990889) ^ 1370293693264449995444 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2740587386528899990889) ^ 210814414348376922376 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2740587386528899990889) ^ 3056484197826904 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 2740587386528899990889) ^ 93251288 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_19157067205583698237009 : Nat.Prime 19157067205583698237009 := by
  apply lucas_primality 19157067205583698237009 (13 : ZMod 19157067205583698237009)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (399105566782993713271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (399105566782993713271, 1)] : List FactorBlock).map factorBlockValue).prod) = 19157067205583698237009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_399105566782993713271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 19157067205583698237009) ^ 9578533602791849118504 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 19157067205583698237009) ^ 6385689068527899412336 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (13 : ZMod 19157067205583698237009) ^ 48 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_21512060194771958817451 : Nat.Prime 21512060194771958817451 := by
  apply lucas_primality 21512060194771958817451 (2 : ZMod 21512060194771958817451)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (58337, 1), (2458366639213759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (58337, 1), (2458366639213759, 1)] : List FactorBlock).map factorBlockValue).prod) = 21512060194771958817451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_58337
      · exact prime_oneHundredFiftyEightEZ_2458366639213759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21512060194771958817451) ^ 10756030097385979408725 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21512060194771958817451) ^ 7170686731590652939150 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21512060194771958817451) ^ 4302412038954391763490 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21512060194771958817451) ^ 368754995882063850 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 21512060194771958817451) ^ 8750550 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_21735193823077270948231 : Nat.Prime 21735193823077270948231 := by
  apply lucas_primality 21735193823077270948231 (7 : ZMod 21735193823077270948231)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (53, 1), (73, 1), (2057795156113379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (53, 1), (73, 1), (2057795156113379, 1)] : List FactorBlock).map factorBlockValue).prod) = 21735193823077270948231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_53
      · exact prime_oneHundredFiftyEightEZ_73
      · exact prime_oneHundredFiftyEightEZ_2057795156113379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 21735193823077270948231) ^ 10867596911538635474115 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 21735193823077270948231) ^ 7245064607692423649410 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 21735193823077270948231) ^ 4347038764615454189646 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 21735193823077270948231) ^ 3105027689011038706890 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 21735193823077270948231) ^ 1671937986390559303710 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 21735193823077270948231) ^ 410097996661835300910 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 21735193823077270948231) ^ 297742381138044807510 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 21735193823077270948231) ^ 10562370 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_35478856765862688553891 : Nat.Prime 35478856765862688553891 := by
  apply lucas_primality 35478856765862688553891 (3 : ZMod 35478856765862688553891)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1987, 1), (625927, 1), (950882401187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1987, 1), (625927, 1), (950882401187, 1)] : List FactorBlock).map factorBlockValue).prod) = 35478856765862688553891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_1987
      · exact prime_oneHundredFiftyEightEZ_625927
      · exact prime_oneHundredFiftyEightEZ_950882401187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35478856765862688553891) ^ 17739428382931344276945 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35478856765862688553891) ^ 11826285588620896184630 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35478856765862688553891) ^ 7095771353172537710778 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35478856765862688553891) ^ 17855489061833260470 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35478856765862688553891) ^ 56682099934757070 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 35478856765862688553891) ^ 37311508470 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_77840224158811426268081 : Nat.Prime 77840224158811426268081 := by
  apply lucas_primality 77840224158811426268081 (6 : ZMod 77840224158811426268081)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1361, 1), (540246799, 1), (1323316609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1361, 1), (540246799, 1), (1323316609, 1)] : List FactorBlock).map factorBlockValue).prod) = 77840224158811426268081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_1361
      · exact prime_oneHundredFiftyEightEZ_540246799
      · exact prime_oneHundredFiftyEightEZ_1323316609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 77840224158811426268081) ^ 38920112079405713134040 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 77840224158811426268081) ^ 15568044831762285253616 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 77840224158811426268081) ^ 57193404966062767280 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 77840224158811426268081) ^ 144082712387920 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 77840224158811426268081) ^ 58822071475120 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_373618752501641985612727 : Nat.Prime 373618752501641985612727 := by
  apply lucas_primality 373618752501641985612727 (3 : ZMod 373618752501641985612727)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (2239, 1), (2377, 1), (10627, 1), (64764130373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (2239, 1), (2377, 1), (10627, 1), (64764130373, 1)] : List FactorBlock).map factorBlockValue).prod) = 373618752501641985612727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_2239
      · exact prime_oneHundredFiftyEightEZ_2377
      · exact prime_oneHundredFiftyEightEZ_10627
      · exact prime_oneHundredFiftyEightEZ_64764130373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 373618752501641985612727) ^ 186809376250820992806363 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 373618752501641985612727) ^ 124539584167213995204242 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 373618752501641985612727) ^ 21977573676567175624278 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 373618752501641985612727) ^ 166868580840393919434 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 373618752501641985612727) ^ 157180796172335711238 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 373618752501641985612727) ^ 35157500000154510738 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 373618752501641985612727) ^ 5768914835262 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_4646605002070743104569417 : Nat.Prime 4646605002070743104569417 := by
  apply lucas_primality 4646605002070743104569417 (5 : ZMod 4646605002070743104569417)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (21512060194771958817451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (21512060194771958817451, 1)] : List FactorBlock).map factorBlockValue).prod) = 4646605002070743104569417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_21512060194771958817451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4646605002070743104569417) ^ 2323302501035371552284708 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 4646605002070743104569417) ^ 1548868334023581034856472 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 4646605002070743104569417) ^ 216 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_4760887136513557537638779 : Nat.Prime 4760887136513557537638779 := by
  apply lucas_primality 4760887136513557537638779 (2 : ZMod 4760887136513557537638779)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (53, 1), (14389, 1), (19759, 1), (4269575747599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (53, 1), (14389, 1), (19759, 1), (4269575747599, 1)] : List FactorBlock).map factorBlockValue).prod) = 4760887136513557537638779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_37
      · exact prime_oneHundredFiftyEightEZ_53
      · exact prime_oneHundredFiftyEightEZ_14389
      · exact prime_oneHundredFiftyEightEZ_19759
      · exact prime_oneHundredFiftyEightEZ_4269575747599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4760887136513557537638779) ^ 2380443568256778768819389 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4760887136513557537638779) ^ 128672625311177230746994 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4760887136513557537638779) ^ 89828059179501085615826 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4760887136513557537638779) ^ 330869910105883490002 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4760887136513557537638779) ^ 240947777545096287142 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 4760887136513557537638779) ^ 1115072648422 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_12703037585055827510832719 : Nat.Prime 12703037585055827510832719 := by
  apply lucas_primality 12703037585055827510832719 (11 : ZMod 12703037585055827510832719)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (373618752501641985612727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (373618752501641985612727, 1)] : List FactorBlock).map factorBlockValue).prod) = 12703037585055827510832719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_17
      · exact prime_oneHundredFiftyEightEZ_373618752501641985612727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 12703037585055827510832719) ^ 6351518792527913755416359 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 12703037585055827510832719) ^ 747237505003283971225454 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 12703037585055827510832719) ^ 34 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_13039101472026102439396561 : Nat.Prime 13039101472026102439396561 := by
  apply lucas_primality 13039101472026102439396561 (14 : ZMod 13039101472026102439396561)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (83, 1), (263, 1), (1253323, 1), (152755276489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (83, 1), (263, 1), (1253323, 1), (152755276489, 1)] : List FactorBlock).map factorBlockValue).prod) = 13039101472026102439396561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_83
      · exact prime_oneHundredFiftyEightEZ_263
      · exact prime_oneHundredFiftyEightEZ_1253323
      · exact prime_oneHundredFiftyEightEZ_152755276489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 13039101472026102439396561) ^ 6519550736013051219698280 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 13039101472026102439396561) ^ 4346367157342034146465520 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 13039101472026102439396561) ^ 2607820294405220487879312 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 13039101472026102439396561) ^ 1003007805540469418415120 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 13039101472026102439396561) ^ 157097608096700029390320 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 13039101472026102439396561) ^ 49578332593255142355120 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 13039101472026102439396561) ^ 10403624183092548720 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (14 : ZMod 13039101472026102439396561) ^ 85359417833040 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_16793865655690546034954161 : Nat.Prime 16793865655690546034954161 := by
  apply lucas_primality 16793865655690546034954161 (22 : ZMod 16793865655690546034954161)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (13, 1), (1069, 1), (1489, 1), (67121, 1), (7197260459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (13, 1), (1069, 1), (1489, 1), (67121, 1), (7197260459, 1)] : List FactorBlock).map factorBlockValue).prod) = 16793865655690546034954161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_1069
      · exact prime_oneHundredFiftyEightEZ_1489
      · exact prime_oneHundredFiftyEightEZ_67121
      · exact prime_oneHundredFiftyEightEZ_7197260459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 16793865655690546034954161) ^ 8396932827845273017477080 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 16793865655690546034954161) ^ 5597955218563515344984720 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 16793865655690546034954161) ^ 3358773131138109206990832 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 16793865655690546034954161) ^ 2399123665098649433564880 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 16793865655690546034954161) ^ 1291835819668503541150320 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 16793865655690546034954161) ^ 15709883681656263830640 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 16793865655690546034954161) ^ 11278620319469809291440 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 16793865655690546034954161) ^ 250202852396277558960 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (22 : ZMod 16793865655690546034954161) ^ 2333369168916240 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_47242834519030334736164677 : Nat.Prime 47242834519030334736164677 := by
  apply lucas_primality 47242834519030334736164677 (2 : ZMod 47242834519030334736164677)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (71, 1), (2640444585235319401753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (71, 1), (2640444585235319401753, 1)] : List FactorBlock).map factorBlockValue).prod) = 47242834519030334736164677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_71
      · exact prime_oneHundredFiftyEightEZ_2640444585235319401753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47242834519030334736164677) ^ 23621417259515167368082338 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 47242834519030334736164677) ^ 15747611506343444912054892 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 47242834519030334736164677) ^ 6748976359861476390880668 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 47242834519030334736164677) ^ 665392035479300489241756 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 47242834519030334736164677) ^ 17892 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_57939878315212761646028267 : Nat.Prime 57939878315212761646028267 := by
  apply lucas_primality 57939878315212761646028267 (2 : ZMod 57939878315212761646028267)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (313, 1), (8425331, 1), (10985410087566511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (313, 1), (8425331, 1), (10985410087566511, 1)] : List FactorBlock).map factorBlockValue).prod) = 57939878315212761646028267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_313
      · exact prime_oneHundredFiftyEightEZ_8425331
      · exact prime_oneHundredFiftyEightEZ_10985410087566511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 57939878315212761646028267) ^ 28969939157606380823014133 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 57939878315212761646028267) ^ 185111432316973679380282 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 57939878315212761646028267) ^ 6876866714816635886 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 57939878315212761646028267) ^ 5274257206 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_105060836720048337202921897 : Nat.Prime 105060836720048337202921897 := by
  apply lucas_primality 105060836720048337202921897 (10 : ZMod 105060836720048337202921897)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (29, 1), (410953, 1), (90316879, 1), (580995139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (29, 1), (410953, 1), (90316879, 1), (580995139, 1)] : List FactorBlock).map factorBlockValue).prod) = 105060836720048337202921897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_29
      · exact prime_oneHundredFiftyEightEZ_410953
      · exact prime_oneHundredFiftyEightEZ_90316879
      · exact prime_oneHundredFiftyEightEZ_580995139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 105060836720048337202921897) ^ 52530418360024168601460948 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 105060836720048337202921897) ^ 35020278906682779067640632 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 105060836720048337202921897) ^ 15008690960006905314703128 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 105060836720048337202921897) ^ 3622787473105115075962824 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 105060836720048337202921897) ^ 255651708881668553832 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 105060836720048337202921897) ^ 1163246979781579224 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (10 : ZMod 105060836720048337202921897) ^ 180829114854347064 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_124698376293889147895056831 : Nat.Prime 124698376293889147895056831 := by
  apply lucas_primality 124698376293889147895056831 (3 : ZMod 124698376293889147895056831)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (131, 1), (433, 1), (95401, 1), (1270249, 1), (604698043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (131, 1), (433, 1), (95401, 1), (1270249, 1), (604698043, 1)] : List FactorBlock).map factorBlockValue).prod) = 124698376293889147895056831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_131
      · exact prime_oneHundredFiftyEightEZ_433
      · exact prime_oneHundredFiftyEightEZ_95401
      · exact prime_oneHundredFiftyEightEZ_1270249
      · exact prime_oneHundredFiftyEightEZ_604698043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 124698376293889147895056831) ^ 62349188146944573947528415 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 124698376293889147895056831) ^ 41566125431296382631685610 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 124698376293889147895056831) ^ 24939675258777829579011366 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 124698376293889147895056831) ^ 951896002243428609885930 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 124698376293889147895056831) ^ 287987012226071935092510 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 124698376293889147895056831) ^ 1307097161391276274830 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 124698376293889147895056831) ^ 98168450669033510670 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 124698376293889147895056831) ^ 206215941555294810 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_662404849958318948747500471 : Nat.Prime 662404849958318948747500471 := by
  apply lucas_primality 662404849958318948747500471 (6 : ZMod 662404849958318948747500471)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (199, 1), (196181, 1), (565577636252618071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (199, 1), (196181, 1), (565577636252618071, 1)] : List FactorBlock).map factorBlockValue).prod) = 662404849958318948747500471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_199
      · exact prime_oneHundredFiftyEightEZ_196181
      · exact prime_oneHundredFiftyEightEZ_565577636252618071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 662404849958318948747500471) ^ 331202424979159474373750235 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 662404849958318948747500471) ^ 220801616652772982915833490 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 662404849958318948747500471) ^ 132480969991663789749500094 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 662404849958318948747500471) ^ 3328667587730245973605530 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 662404849958318948747500471) ^ 3376498488428129883870 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (6 : ZMod 662404849958318948747500471) ^ 1171200570 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_1698165160802235850425410299 : Nat.Prime 1698165160802235850425410299 := by
  apply lucas_primality 1698165160802235850425410299 (2 : ZMod 1698165160802235850425410299)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14851, 1), (27232319, 1), (699823226940907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14851, 1), (27232319, 1), (699823226940907, 1)] : List FactorBlock).map factorBlockValue).prod) = 1698165160802235850425410299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_14851
      · exact prime_oneHundredFiftyEightEZ_27232319
      · exact prime_oneHundredFiftyEightEZ_699823226940907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1698165160802235850425410299) ^ 849082580401117925212705149 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1698165160802235850425410299) ^ 566055053600745283475136766 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1698165160802235850425410299) ^ 114346856157985041439998 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1698165160802235850425410299) ^ 62358448459796459142 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 1698165160802235850425410299) ^ 2426563016814 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_2490642235843279247290601771 : Nat.Prime 2490642235843279247290601771 := by
  apply lucas_primality 2490642235843279247290601771 (2 : ZMod 2490642235843279247290601771)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (633427, 1), (647367397, 1), (607384847983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (633427, 1), (647367397, 1), (607384847983, 1)] : List FactorBlock).map factorBlockValue).prod) = 2490642235843279247290601771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_633427
      · exact prime_oneHundredFiftyEightEZ_647367397
      · exact prime_oneHundredFiftyEightEZ_607384847983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2490642235843279247290601771) ^ 1245321117921639623645300885 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2490642235843279247290601771) ^ 498128447168655849458120354 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2490642235843279247290601771) ^ 3932011480159954102510 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2490642235843279247290601771) ^ 3847339621033277410 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 2490642235843279247290601771) ^ 4100599881795190 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_3662709170357763598956767311 : Nat.Prime 3662709170357763598956767311 := by
  apply lucas_primality 3662709170357763598956767311 (3 : ZMod 3662709170357763598956767311)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (109, 1), (102333389, 1), (82297318572269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (109, 1), (102333389, 1), (82297318572269, 1)] : List FactorBlock).map factorBlockValue).prod) = 3662709170357763598956767311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_109
      · exact prime_oneHundredFiftyEightEZ_102333389
      · exact prime_oneHundredFiftyEightEZ_82297318572269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3662709170357763598956767311) ^ 1831354585178881799478383655 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3662709170357763598956767311) ^ 1220903056785921199652255770 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3662709170357763598956767311) ^ 732541834071552719791353462 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3662709170357763598956767311) ^ 523244167193966228422395330 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3662709170357763598956767311) ^ 192774166860934926260882490 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3662709170357763598956767311) ^ 33602836425300583476667590 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3662709170357763598956767311) ^ 35791926820265510790 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (3 : ZMod 3662709170357763598956767311) ^ 44505814209990 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_8490825804011179252127051491 : Nat.Prime 8490825804011179252127051491 := by
  apply lucas_primality 8490825804011179252127051491 (2 : ZMod 8490825804011179252127051491)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (14851, 1), (27232319, 1), (699823226940907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (14851, 1), (27232319, 1), (699823226940907, 1)] : List FactorBlock).map factorBlockValue).prod) = 8490825804011179252127051491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_14851
      · exact prime_oneHundredFiftyEightEZ_27232319
      · exact prime_oneHundredFiftyEightEZ_699823226940907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8490825804011179252127051491) ^ 4245412902005589626063525745 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8490825804011179252127051491) ^ 2830275268003726417375683830 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8490825804011179252127051491) ^ 1698165160802235850425410298 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8490825804011179252127051491) ^ 571734280789925207199990 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8490825804011179252127051491) ^ 311792242298982295710 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 8490825804011179252127051491) ^ 12132815084070 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_12453211179216396236453008859 : Nat.Prime 12453211179216396236453008859 := by
  apply lucas_primality 12453211179216396236453008859 (2 : ZMod 12453211179216396236453008859)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (13209857, 1), (15205179346458550387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (13209857, 1), (15205179346458550387, 1)] : List FactorBlock).map factorBlockValue).prod) = 12453211179216396236453008859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_31
      · exact prime_oneHundredFiftyEightEZ_13209857
      · exact prime_oneHundredFiftyEightEZ_15205179346458550387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12453211179216396236453008859) ^ 6226605589608198118226504429 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12453211179216396236453008859) ^ 401716489652141814079129318 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12453211179216396236453008859) ^ 942721119480430123994 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 12453211179216396236453008859) ^ 819011134 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_23349770961030742943349391607 : Nat.Prime 23349770961030742943349391607 := by
  apply lucas_primality 23349770961030742943349391607 (5 : ZMod 23349770961030742943349391607)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (59, 1), (15139, 1), (687938836688752114537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (59, 1), (15139, 1), (687938836688752114537, 1)] : List FactorBlock).map factorBlockValue).prod) = 23349770961030742943349391607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_19
      · exact prime_oneHundredFiftyEightEZ_59
      · exact prime_oneHundredFiftyEightEZ_15139
      · exact prime_oneHundredFiftyEightEZ_687938836688752114537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23349770961030742943349391607) ^ 11674885480515371471674695803 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 23349770961030742943349391607) ^ 1228935313738460154913125874 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 23349770961030742943349391607) ^ 395758829847978693955074434 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 23349770961030742943349391607) ^ 1542358871856182240791954 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (5 : ZMod 23349770961030742943349391607) ^ 33941638 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_23349770961030742943349391609 : Nat.Prime 23349770961030742943349391609 := by
  apply lucas_primality 23349770961030742943349391609 (7 : ZMod 23349770961030742943349391609)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (10663, 1), (1486241, 1), (20463573774419233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (10663, 1), (1486241, 1), (20463573774419233, 1)] : List FactorBlock).map factorBlockValue).prod) = 23349770961030742943349391609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_10663
      · exact prime_oneHundredFiftyEightEZ_1486241
      · exact prime_oneHundredFiftyEightEZ_20463573774419233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23349770961030742943349391609) ^ 11674885480515371471674695804 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 23349770961030742943349391609) ^ 7783256987010247647783130536 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 23349770961030742943349391609) ^ 2189793769204796299667016 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 23349770961030742943349391609) ^ 15710622275277524266488 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (7 : ZMod 23349770961030742943349391609) ^ 1141040720376 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_93399083844122971773397566413 : Nat.Prime 93399083844122971773397566413 := by
  apply lucas_primality 93399083844122971773397566413 (2 : ZMod 93399083844122971773397566413)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (3900738859271, 1), (77740087110409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (3900738859271, 1), (77740087110409, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122971773397566413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_7
      · exact prime_oneHundredFiftyEightEZ_11
      · exact prime_oneHundredFiftyEightEZ_3900738859271
      · exact prime_oneHundredFiftyEightEZ_77740087110409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93399083844122971773397566413) ^ 46699541922061485886698783206 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93399083844122971773397566413) ^ 13342726263446138824771080916 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93399083844122971773397566413) ^ 8490825804011179252127051492 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93399083844122971773397566413) ^ 23943946830005972 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 93399083844122971773397566413) ^ 1201427568655468 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_93399083844122971773397566431 : Nat.Prime 93399083844122971773397566431 := by
  apply lucas_primality 93399083844122971773397566431 (19 : ZMod 93399083844122971773397566431)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (691, 1), (11617, 1), (89500863873037785013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (691, 1), (11617, 1), (89500863873037785013, 1)] : List FactorBlock).map factorBlockValue).prod) = 93399083844122971773397566431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_5
      · exact prime_oneHundredFiftyEightEZ_13
      · exact prime_oneHundredFiftyEightEZ_691
      · exact prime_oneHundredFiftyEightEZ_11617
      · exact prime_oneHundredFiftyEightEZ_89500863873037785013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 93399083844122971773397566431) ^ 46699541922061485886698783215 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 93399083844122971773397566431) ^ 18679816768824594354679513286 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 93399083844122971773397566431) ^ 7184544911086382444107505110 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 93399083844122971773397566431) ^ 135165099629700393304482730 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 93399083844122971773397566431) ^ 8039862601714984227717790 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (19 : ZMod 93399083844122971773397566431) ^ 1043555110 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_186798167688245943546795132883 : Nat.Prime 186798167688245943546795132883 := by
  apply lucas_primality 186798167688245943546795132883 (2 : ZMod 186798167688245943546795132883)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (379, 1), (93557, 1), (9527149, 1), (30720031178467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (379, 1), (93557, 1), (9527149, 1), (30720031178467, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_379
      · exact prime_oneHundredFiftyEightEZ_93557
      · exact prime_oneHundredFiftyEightEZ_9527149
      · exact prime_oneHundredFiftyEightEZ_30720031178467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 186798167688245943546795132883) ^ 93399083844122971773397566441 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 186798167688245943546795132883) ^ 62266055896081981182265044294 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 186798167688245943546795132883) ^ 492871154850253149199987158 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 186798167688245943546795132883) ^ 1996624172304006579377226 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 186798167688245943546795132883) ^ 19606932534407296825818 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (2 : ZMod 186798167688245943546795132883) ^ 6080663349690246 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyEightEZ_186798167688245943546795132889 : Nat.Prime 186798167688245943546795132889 := by
  apply lucas_primality 186798167688245943546795132889 (11 : ZMod 186798167688245943546795132889)
  · rw [← oneHundredFiftyEightEZFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (269, 1), (883, 1), (14489, 1), (407893, 1), (5544517031803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (269, 1), (883, 1), (14489, 1), (407893, 1), (5544517031803, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyEightEZ_2
      · exact prime_oneHundredFiftyEightEZ_3
      · exact prime_oneHundredFiftyEightEZ_269
      · exact prime_oneHundredFiftyEightEZ_883
      · exact prime_oneHundredFiftyEightEZ_14489
      · exact prime_oneHundredFiftyEightEZ_407893
      · exact prime_oneHundredFiftyEightEZ_5544517031803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 186798167688245943546795132889) ^ 93399083844122971773397566444 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 186798167688245943546795132889) ^ 62266055896081981182265044296 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 186798167688245943546795132889) ^ 694416980253702392367268152 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 186798167688245943546795132889) ^ 211549453780572982499201736 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 186798167688245943546795132889) ^ 12892412705379663437559192 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 186798167688245943546795132889) ^ 457958748221337320196216 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide
    · change (11 : ZMod 186798167688245943546795132889) ^ 33690611214066696 ≠ 1
      rw [← oneHundredFiftyEightEZFastPow_eq_pow]
      decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132800 : Nat.totient 186798167688245943546795132800 = 73773023038106923735087104000 := by
  rw [← show ((([(2, 7), (5, 2), (79, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_79, prime_oneHundredFiftyEightEZ_171401, prime_oneHundredFiftyEightEZ_714027719, prime_oneHundredFiftyEightEZ_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132801 : Nat.totient 186798167688245943546795132801 = 123244014171458025345850481664 := by
  rw [← show ((([(3, 2), (97, 1), (29027, 1), (7987669, 1), (922860707248199, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_97, prime_oneHundredFiftyEightEZ_29027, prime_oneHundredFiftyEightEZ_7987669, prime_oneHundredFiftyEightEZ_922860707248199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132802 : Nat.totient 186798167688245943546795132802 = 84908258040111792521270514900 := by
  rw [← show ((([(2, 1), (11, 1), (8490825804011179252127051491, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_11, prime_oneHundredFiftyEightEZ_8490825804011179252127051491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132803 : Nat.totient 186798167688245943546795132803 = 159407372803814662963784886720 := by
  rw [← show ((([(7, 2), (227, 1), (16793865655690546034954161, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_227, prime_oneHundredFiftyEightEZ_16793865655690546034954161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132804 : Nat.totient 186798167688245943546795132804 = 62251275628025834203266854400 := by
  rw [← show ((([(2, 2), (3, 1), (4217, 1), (4211371, 1), (876524909588327081, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_4217, prime_oneHundredFiftyEightEZ_4211371, prime_oneHundredFiftyEightEZ_876524909588327081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132805 : Nat.totient 186798167688245943546795132805 = 149426800397989552801539816768 := by
  rw [← show ((([(5, 1), (12763, 1), (5971919, 1), (490157813223534013, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_12763, prime_oneHundredFiftyEightEZ_5971919, prime_oneHundredFiftyEightEZ_490157813223534013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132806 : Nat.totient 186798167688245943546795132806 = 93219495333707891519576964000 := by
  rw [← show ((([(2, 1), (571, 1), (5821, 1), (274252331, 1), (102460997871143, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_571, prime_oneHundredFiftyEightEZ_5821, prime_oneHundredFiftyEightEZ_274252331, prime_oneHundredFiftyEightEZ_102460997871143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132807 : Nat.totient 186798167688245943546795132807 = 124532093776084039693560431520 := by
  rw [← show ((([(3, 1), (8561011, 1), (35891797, 1), (202642763460707, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_8561011, prime_oneHundredFiftyEightEZ_35891797, prime_oneHundredFiftyEightEZ_202642763460707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132808 : Nat.totient 186798167688245943546795132808 = 83433424773906376770280703040 := by
  rw [← show ((([(2, 3), (13, 1), (31, 1), (57939878315212761646028267, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_13, prime_oneHundredFiftyEightEZ_31, prime_oneHundredFiftyEightEZ_57939878315212761646028267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132809 : Nat.totient 186798167688245943546795132809 = 175256812513692827155510272000 := by
  rw [← show ((([(23, 1), (71, 1), (353, 1), (757, 1), (1031, 1), (92941, 1), (4467348527903, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_23, prime_oneHundredFiftyEightEZ_71, prime_oneHundredFiftyEightEZ_353, prime_oneHundredFiftyEightEZ_757, prime_oneHundredFiftyEightEZ_1031, prime_oneHundredFiftyEightEZ_92941, prime_oneHundredFiftyEightEZ_4467348527903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132810 : Nat.totient 186798167688245943546795132810 = 37720876293258269552789520384 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (7, 1), (17, 1), (19, 1), (109, 1), (102333389, 1), (82297318572269, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_17, prime_oneHundredFiftyEightEZ_19, prime_oneHundredFiftyEightEZ_109, prime_oneHundredFiftyEightEZ_102333389, prime_oneHundredFiftyEightEZ_82297318572269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132811 : Nat.totient 186798167688245943546795132811 = 186514180606971531338534378400 := by
  rw [← show ((([(1291, 1), (1667, 1), (6827, 1), (271011371, 1), (46913015939, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_1291, prime_oneHundredFiftyEightEZ_1667, prime_oneHundredFiftyEightEZ_6827, prime_oneHundredFiftyEightEZ_271011371, prime_oneHundredFiftyEightEZ_46913015939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132812 : Nat.totient 186798167688245943546795132812 = 93399083686451573597426788896 := by
  rw [← show ((([(2, 2), (592365419, 1), (78835699087393023337, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_592365419, prime_oneHundredFiftyEightEZ_78835699087393023337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132813 : Nat.totient 186798167688245943546795132813 = 113210920360348969854833141760 := by
  rw [← show ((([(3, 1), (11, 1), (2397007, 1), (2624899, 1), (899656604027777, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_11, prime_oneHundredFiftyEightEZ_2397007, prime_oneHundredFiftyEightEZ_2624899, prime_oneHundredFiftyEightEZ_899656604027777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132814 : Nat.totient 186798167688245943546795132814 = 91121057408663985004914456000 := by
  rw [← show ((([(2, 1), (41, 1), (385355308027, 1), (5911496190063901, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_41, prime_oneHundredFiftyEightEZ_385355308027, prime_oneHundredFiftyEightEZ_5911496190063901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132815 : Nat.totient 186798167688245943546795132815 = 149428477143215177890911136416 := by
  rw [← show ((([(5, 1), (14923, 1), (3472387, 1), (720971914273780963, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_14923, prime_oneHundredFiftyEightEZ_3472387, prime_oneHundredFiftyEightEZ_720971914273780963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132816 : Nat.totient 186798167688245943546795132816 = 62244420857472664707922851840 := by
  rw [← show ((([(2, 4), (3, 1), (3313, 1), (28463, 1), (95231, 1), (433362093971603, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_3313, prime_oneHundredFiftyEightEZ_28463, prime_oneHundredFiftyEightEZ_95231, prime_oneHundredFiftyEightEZ_433362093971603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132817 : Nat.totient 186798167688245943546795132817 = 160084835531341241438625520032 := by
  rw [← show ((([(7, 1), (5743, 1), (4646605002070743104569417, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_5743, prime_oneHundredFiftyEightEZ_4646605002070743104569417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132818 : Nat.totient 186798167688245943546795132818 = 93391242550270968129851804160 := by
  rw [← show ((([(2, 1), (12253, 1), (426941, 1), (17853868007922800033, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_12253, prime_oneHundredFiftyEightEZ_426941, prime_oneHundredFiftyEightEZ_17853868007922800033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132819 : Nat.totient 186798167688245943546795132819 = 123651050381920708900382638080 := by
  rw [← show ((([(3, 4), (157, 1), (1409, 1), (2884513, 1), (3614135632786271, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_157, prime_oneHundredFiftyEightEZ_1409, prime_oneHundredFiftyEightEZ_2884513, prime_oneHundredFiftyEightEZ_3614135632786271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132820 : Nat.totient 186798167688245943546795132820 = 74719267075183928511011258400 := by
  rw [← show ((([(2, 2), (5, 1), (652891134631, 1), (14305460572214711, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_652891134631, prime_oneHundredFiftyEightEZ_14305460572214711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132821 : Nat.totient 186798167688245943546795132821 = 172429074701064929030534544384 := by
  rw [← show ((([(13, 1), (56044717, 1), (1980986257, 1), (129423492893, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_13, prime_oneHundredFiftyEightEZ_56044717, prime_oneHundredFiftyEightEZ_1980986257, prime_oneHundredFiftyEightEZ_129423492893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132822 : Nat.totient 186798167688245943546795132822 = 60941246196165343284770043240 := by
  rw [← show ((([(2, 1), (3, 1), (47, 1), (662404849958318948747500471, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_47, prime_oneHundredFiftyEightEZ_662404849958318948747500471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132823 : Nat.totient 186798167688245943546795132823 = 186439903969672633739110778112 := by
  rw [← show ((([(557, 1), (8387, 1), (369827, 1), (1147507, 1), (94222975673, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_557, prime_oneHundredFiftyEightEZ_8387, prime_oneHundredFiftyEightEZ_369827, prime_oneHundredFiftyEightEZ_1147507, prime_oneHundredFiftyEightEZ_94222975673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132824 : Nat.totient 186798167688245943546795132824 = 72778506891504799791427718400 := by
  rw [← show ((([(2, 3), (7, 1), (11, 1), (3900738859271, 1), (77740087110409, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_11, prime_oneHundredFiftyEightEZ_3900738859271, prime_oneHundredFiftyEightEZ_77740087110409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132825 : Nat.totient 186798167688245943546795132825 = 99625689433731169891624070800 := by
  rw [← show ((([(3, 1), (5, 2), (2490642235843279247290601771, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_2490642235843279247290601771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132826 : Nat.totient 186798167688245943546795132826 = 93399083844122971773397566412 := by
  rw [← show ((([(2, 1), (93399083844122971773397566413, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_93399083844122971773397566413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132827 : Nat.totient 186798167688245943546795132827 = 175806291958064549601260158080 := by
  rw [← show ((([(17, 1), (86291, 1), (102763, 1), (1239142961267146907, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_17, prime_oneHundredFiftyEightEZ_86291, prime_oneHundredFiftyEightEZ_102763, prime_oneHundredFiftyEightEZ_1239142961267146907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132828 : Nat.totient 186798167688245943546795132828 = 57348894321331250825697269760 := by
  rw [← show ((([(2, 2), (3, 2), (29, 1), (37, 1), (53, 1), (1381, 1), (66069472740616929607, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_29, prime_oneHundredFiftyEightEZ_37, prime_oneHundredFiftyEightEZ_53, prime_oneHundredFiftyEightEZ_1381, prime_oneHundredFiftyEightEZ_66069472740616929607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132829 : Nat.totient 186798167688245943546795132829 = 176662188279937046395424360448 := by
  rw [← show ((([(19, 1), (839, 1), (1889, 1), (1826370709, 1), (3396535505269, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_19, prime_oneHundredFiftyEightEZ_839, prime_oneHundredFiftyEightEZ_1889, prime_oneHundredFiftyEightEZ_1826370709, prime_oneHundredFiftyEightEZ_3396535505269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132830 : Nat.totient 186798167688245943546795132830 = 74057324104988314873370022400 := by
  rw [← show ((([(2, 1), (5, 1), (113, 1), (104231, 1), (1585978384534809583061, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_113, prime_oneHundredFiftyEightEZ_104231, prime_oneHundredFiftyEightEZ_1585978384534809583061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132831 : Nat.totient 186798167688245943546795132831 = 106271432552293941600403361280 := by
  rw [← show ((([(3, 1), (7, 1), (271, 1), (1543, 1), (14033, 1), (1515889605573545339, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_271, prime_oneHundredFiftyEightEZ_1543, prime_oneHundredFiftyEightEZ_14033, prime_oneHundredFiftyEightEZ_1515889605573545339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132832 : Nat.totient 186798167688245943546795132832 = 89330603323544075888219784960 := by
  rw [← show ((([(2, 5), (23, 1), (11677, 1), (21735193823077270948231, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_23, prime_oneHundredFiftyEightEZ_11677, prime_oneHundredFiftyEightEZ_21735193823077270948231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132833 : Nat.totient 186798167688245943546795132833 = 186352348662476814794375370400 := by
  rw [← show ((([(419, 1), (19002515507, 1), (23461052606333801, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_419, prime_oneHundredFiftyEightEZ_19002515507, prime_oneHundredFiftyEightEZ_23461052606333801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132834 : Nat.totient 186798167688245943546795132834 = 57476344308901428764624330112 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (3836927, 1), (624157901282839317689, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_13, prime_oneHundredFiftyEightEZ_3836927, prime_oneHundredFiftyEightEZ_624157901282839317689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132835 : Nat.totient 186798167688245943546795132835 = 131723325976192189495829959680 := by
  rw [← show ((([(5, 1), (11, 1), (43, 1), (139, 1), (8297, 1), (68486595296926186613, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_11, prime_oneHundredFiftyEightEZ_43, prime_oneHundredFiftyEightEZ_139, prime_oneHundredFiftyEightEZ_8297, prime_oneHundredFiftyEightEZ_68486595296926186613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132836 : Nat.totient 186798167688245943546795132836 = 92255703389877230091697534752 := by
  rw [← show ((([(2, 2), (83, 1), (5119, 1), (1429403, 1), (76894399445572439, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_83, prime_oneHundredFiftyEightEZ_5119, prime_oneHundredFiftyEightEZ_1429403, prime_oneHundredFiftyEightEZ_76894399445572439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132837 : Nat.totient 186798167688245943546795132837 = 124211970909657714311412307200 := by
  rw [← show ((([(3, 2), (389, 1), (19877191, 1), (187810361, 1), (14292425687, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_389, prime_oneHundredFiftyEightEZ_19877191, prime_oneHundredFiftyEightEZ_187810361, prime_oneHundredFiftyEightEZ_14292425687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132838 : Nat.totient 186798167688245943546795132838 = 79308167322913498061256143880 := by
  rw [← show ((([(2, 1), (7, 1), (107, 1), (124698376293889147895056831, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_107, prime_oneHundredFiftyEightEZ_124698376293889147895056831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132839 : Nat.totient 186798167688245943546795132839 = 180572312252216793634951680000 := by
  rw [← show ((([(31, 1), (1873, 1), (2347, 1), (6791, 1), (10216901, 1), (19756369289, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_31, prime_oneHundredFiftyEightEZ_1873, prime_oneHundredFiftyEightEZ_2347, prime_oneHundredFiftyEightEZ_6791, prime_oneHundredFiftyEightEZ_10216901, prime_oneHundredFiftyEightEZ_19756369289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132840 : Nat.totient 186798167688245943546795132840 = 49545621963296740114544885760 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (191, 1), (8017, 1), (205033, 1), (4958180680080557, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_191, prime_oneHundredFiftyEightEZ_8017, prime_oneHundredFiftyEightEZ_205033, prime_oneHundredFiftyEightEZ_4958180680080557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132841 : Nat.totient 186798167688245943546795132841 = 186798166304685385531023439812 := by
  rw [← show ((([(135012643, 1), (1383560558015636680387, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_135012643, prime_oneHundredFiftyEightEZ_1383560558015636680387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132842 : Nat.totient 186798167688245943546795132842 = 92178925125634771068759206400 := by
  rw [← show ((([(2, 1), (89, 1), (541, 1), (3205871, 1), (403357067, 1), (1500097997, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_89, prime_oneHundredFiftyEightEZ_541, prime_oneHundredFiftyEightEZ_3205871, prime_oneHundredFiftyEightEZ_403357067, prime_oneHundredFiftyEightEZ_1500097997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132843 : Nat.totient 186798167688245943546795132843 = 124526119186081813334025669120 := by
  rw [← show ((([(3, 1), (21313, 1), (832427, 1), (3509624183824913131, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_21313, prime_oneHundredFiftyEightEZ_832427, prime_oneHundredFiftyEightEZ_3509624183824913131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132844 : Nat.totient 186798167688245943546795132844 = 87752671700217892533757956096 := by
  rw [← show ((([(2, 2), (17, 1), (577, 1), (4760887136513557537638779, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_17, prime_oneHundredFiftyEightEZ_577, prime_oneHundredFiftyEightEZ_4760887136513557537638779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132845 : Nat.totient 186798167688245943546795132845 = 127993060550293355986198419456 := by
  rw [← show ((([(5, 1), (7, 1), (1319, 1), (629711430577, 1), (6425666705609, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_1319, prime_oneHundredFiftyEightEZ_629711430577, prime_oneHundredFiftyEightEZ_6425666705609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132846 : Nat.totient 186798167688245943546795132846 = 56503356392815909829401248000 := by
  rw [← show ((([(2, 1), (3, 3), (11, 2), (653, 1), (3671, 1), (835453, 1), (14274926905571, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_11, prime_oneHundredFiftyEightEZ_653, prime_oneHundredFiftyEightEZ_3671, prime_oneHundredFiftyEightEZ_835453, prime_oneHundredFiftyEightEZ_14274926905571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132847 : Nat.totient 186798167688245943546795132847 = 171535244412871637151644344320 := by
  rw [← show ((([(13, 1), (193, 1), (409841, 1), (181658844776221569563, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_13, prime_oneHundredFiftyEightEZ_193, prime_oneHundredFiftyEightEZ_409841, prime_oneHundredFiftyEightEZ_181658844776221569563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132848 : Nat.totient 186798167688245943546795132848 = 86977879253002240066233524736 := by
  rw [← show ((([(2, 4), (19, 1), (59, 1), (15139, 1), (687938836688752114537, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_19, prime_oneHundredFiftyEightEZ_59, prime_oneHundredFiftyEightEZ_15139, prime_oneHundredFiftyEightEZ_687938836688752114537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132849 : Nat.totient 186798167688245943546795132849 = 122490601759817779014972360000 := by
  rw [← show ((([(3, 1), (61, 1), (41292103603, 1), (24720344221351501, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_61, prime_oneHundredFiftyEightEZ_41292103603, prime_oneHundredFiftyEightEZ_24720344221351501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132850 : Nat.totient 186798167688245943546795132850 = 73677008115090073797125160960 := by
  rw [← show ((([(2, 1), (5, 2), (73, 1), (4517, 1), (30817, 1), (57301759, 1), (6416103259, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_73, prime_oneHundredFiftyEightEZ_4517, prime_oneHundredFiftyEightEZ_30817, prime_oneHundredFiftyEightEZ_57301759, prime_oneHundredFiftyEightEZ_6416103259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132851 : Nat.totient 186798167688245943546795132851 = 186587409330738536179575582088 := by
  rw [← show ((([(887, 1), (1145387, 1), (183864016257390138479, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_887, prime_oneHundredFiftyEightEZ_1145387, prime_oneHundredFiftyEightEZ_183864016257390138479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132852 : Nat.totient 186798167688245943546795132852 = 53370901556118877983144173568 := by
  rw [← show ((([(2, 2), (3, 1), (7, 2), (15259007, 1), (20819438555436765697, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_15259007, prime_oneHundredFiftyEightEZ_20819438555436765697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132853 : Nat.totient 186798167688245943546795132853 = 184008707933080536020506622400 := by
  rw [← show ((([(67, 1), (196477, 1), (377231, 1), (67269331, 1), (559192847, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_67, prime_oneHundredFiftyEightEZ_196477, prime_oneHundredFiftyEightEZ_377231, prime_oneHundredFiftyEightEZ_67269331, prime_oneHundredFiftyEightEZ_559192847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132854 : Nat.totient 186798167688245943546795132854 = 93396460361787933587756588160 := by
  rw [← show ((([(2, 1), (36011, 1), (3128249, 1), (829098482468746393, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_36011, prime_oneHundredFiftyEightEZ_3128249, prime_oneHundredFiftyEightEZ_829098482468746393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132855 : Nat.totient 186798167688245943546795132855 = 92969890320329125875385320960 := by
  rw [← show ((([(3, 2), (5, 1), (23, 1), (41, 1), (676402619, 1), (6507933775024807, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_23, prime_oneHundredFiftyEightEZ_41, prime_oneHundredFiftyEightEZ_676402619, prime_oneHundredFiftyEightEZ_6507933775024807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132856 : Nat.totient 186798167688245943546795132856 = 93399083844122971773397566424 := by
  rw [← show ((([(2, 3), (23349770961030742943349391607, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_23349770961030742943349391607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132857 : Nat.totient 186798167688245943546795132857 = 163947364744416741257257555200 := by
  rw [← show ((([(11, 1), (29, 1), (12823, 1), (282847, 1), (3786011, 1), (42644088733, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_11, prime_oneHundredFiftyEightEZ_29, prime_oneHundredFiftyEightEZ_12823, prime_oneHundredFiftyEightEZ_282847, prime_oneHundredFiftyEightEZ_3786011, prime_oneHundredFiftyEightEZ_42644088733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132858 : Nat.totient 186798167688245943546795132858 = 62171570227043920512792713616 := by
  rw [← show ((([(2, 1), (3, 1), (659, 1), (47242834519030334736164677, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_659, prime_oneHundredFiftyEightEZ_47242834519030334736164677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132859 : Nat.totient 186798167688245943546795132859 = 159441258510294724139122457280 := by
  rw [← show ((([(7, 1), (239, 1), (104281, 1), (1070709075317951374043, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_239, prime_oneHundredFiftyEightEZ_104281, prime_oneHundredFiftyEightEZ_1070709075317951374043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132860 : Nat.totient 186798167688245943546795132860 = 68865888381787465764727726080 := by
  rw [← show ((([(2, 2), (5, 1), (13, 1), (691, 1), (11617, 1), (89500863873037785013, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_13, prime_oneHundredFiftyEightEZ_691, prime_oneHundredFiftyEightEZ_11617, prime_oneHundredFiftyEightEZ_89500863873037785013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132861 : Nat.totient 186798167688245943546795132861 = 117206693451448435166616553920 := by
  rw [← show ((([(3, 1), (17, 1), (3662709170357763598956767311, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_17, prime_oneHundredFiftyEightEZ_3662709170357763598956767311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132862 : Nat.totient 186798167688245943546795132862 = 93399083844122971773397566430 := by
  rw [← show ((([(2, 1), (93399083844122971773397566431, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_93399083844122971773397566431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132863 : Nat.totient 186798167688245943546795132863 = 186798167686799705454103742640 := by
  rw [← show ((([(129161432903, 1), (1446237963529957321, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_129161432903, prime_oneHundredFiftyEightEZ_1446237963529957321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132864 : Nat.totient 186798167688245943546795132864 = 62260174554967037440935198720 := by
  rw [← show ((([(2, 6), (3, 2), (10663, 1), (1486241, 1), (20463573774419233, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_10663, prime_oneHundredFiftyEightEZ_1486241, prime_oneHundredFiftyEightEZ_20463573774419233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132865 : Nat.totient 186798167688245943546795132865 = 145388293045662055117169574144 := by
  rw [← show ((([(5, 1), (37, 1), (12829, 1), (5167823, 1), (15230019096283987, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_37, prime_oneHundredFiftyEightEZ_12829, prime_oneHundredFiftyEightEZ_5167823, prime_oneHundredFiftyEightEZ_15230019096283987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132866 : Nat.totient 186798167688245943546795132866 = 79425992560356542925408953376 := by
  rw [← show ((([(2, 1), (7, 1), (127, 1), (105060836720048337202921897, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_127, prime_oneHundredFiftyEightEZ_105060836720048337202921897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132867 : Nat.totient 186798167688245943546795132867 = 116823933629836810899155988480 := by
  rw [← show ((([(3, 1), (19, 1), (103, 1), (13841, 1), (7818212393, 1), (294025907029, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_19, prime_oneHundredFiftyEightEZ_103, prime_oneHundredFiftyEightEZ_13841, prime_oneHundredFiftyEightEZ_7818212393, prime_oneHundredFiftyEightEZ_294025907029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132868 : Nat.totient 186798167688245943546795132868 = 83842199955023800529398464000 := by
  rw [← show ((([(2, 2), (11, 1), (101, 1), (373, 1), (16975148767, 1), (6638594484517, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_11, prime_oneHundredFiftyEightEZ_101, prime_oneHundredFiftyEightEZ_373, prime_oneHundredFiftyEightEZ_16975148767, prime_oneHundredFiftyEightEZ_6638594484517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132869 : Nat.totient 186798167688245943546795132869 = 182766872211539795099506451712 := by
  rw [← show ((([(47, 1), (3217, 1), (5095157, 1), (242474527855275983, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_47, prime_oneHundredFiftyEightEZ_3217, prime_oneHundredFiftyEightEZ_5095157, prime_oneHundredFiftyEightEZ_242474527855275983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132870 : Nat.totient 186798167688245943546795132870 = 48205975109013974536273059840 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (31, 1), (13209857, 1), (15205179346458550387, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_31, prime_oneHundredFiftyEightEZ_13209857, prime_oneHundredFiftyEightEZ_15205179346458550387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132871 : Nat.totient 186798167688245943546795132871 = 186772137930305701000208201880 := by
  rw [← show ((([(7639, 1), (118471, 1), (206406822195422576359, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_7639, prime_oneHundredFiftyEightEZ_118471, prime_oneHundredFiftyEightEZ_206406822195422576359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132872 : Nat.totient 186798167688245943546795132872 = 93399083844122971773397566432 := by
  rw [← show ((([(2, 3), (23349770961030742943349391609, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_23349770961030742943349391609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132873 : Nat.totient 186798167688245943546795132873 = 98530841423299975031166453504 := by
  rw [← show ((([(3, 3), (7, 1), (13, 1), (1636333, 1), (46461771702976334933, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_13, prime_oneHundredFiftyEightEZ_1636333, prime_oneHundredFiftyEightEZ_46461771702976334933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132874 : Nat.totient 186798167688245943546795132874 = 92980226799930630868748329392 := by
  rw [← show ((([(2, 1), (223, 1), (3439747, 1), (2394091559, 1), (50859313903, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_223, prime_oneHundredFiftyEightEZ_3439747, prime_oneHundredFiftyEightEZ_2394091559, prime_oneHundredFiftyEightEZ_50859313903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132875 : Nat.totient 186798167688245943546795132875 = 149436618443876196467604604800 := by
  rw [← show ((([(5, 3), (78007, 1), (19157067205583698237009, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_78007, prime_oneHundredFiftyEightEZ_19157067205583698237009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132876 : Nat.totient 186798167688245943546795132876 = 62121587060519289185430408960 := by
  rw [← show ((([(2, 2), (3, 1), (431, 1), (2188982767, 1), (16499536835262449, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_431, prime_oneHundredFiftyEightEZ_2188982767, prime_oneHundredFiftyEightEZ_16499536835262449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132877 : Nat.totient 186798167688245943546795132877 = 186780546861871352199896997600 := by
  rw [← show ((([(10601, 1), (9308831339, 1), (1892912833836943, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_10601, prime_oneHundredFiftyEightEZ_9308831339, prime_oneHundredFiftyEightEZ_1892912833836943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132878 : Nat.totient 186798167688245943546795132878 = 82087125786870039624673876992 := by
  rw [← show ((([(2, 1), (17, 1), (23, 1), (43, 1), (2027, 1), (2740587386528899990889, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_17, prime_oneHundredFiftyEightEZ_23, prime_oneHundredFiftyEightEZ_43, prime_oneHundredFiftyEightEZ_2027, prime_oneHundredFiftyEightEZ_2740587386528899990889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132879 : Nat.totient 186798167688245943546795132879 = 111533898059320716454161024000 := by
  rw [← show ((([(3, 1), (11, 1), (79, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_11, prime_oneHundredFiftyEightEZ_79, prime_oneHundredFiftyEightEZ_461, prime_oneHundredFiftyEightEZ_69997, prime_oneHundredFiftyEightEZ_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132880 : Nat.totient 186798167688245943546795132880 = 63130800058304797356975360000 := by
  rw [← show ((([(2, 4), (5, 1), (7, 1), (71, 1), (5303, 1), (188171, 1), (4708167619799101, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_71, prime_oneHundredFiftyEightEZ_5303, prime_oneHundredFiftyEightEZ_188171, prime_oneHundredFiftyEightEZ_4708167619799101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132881 : Nat.totient 186798167688245943546795132881 = 183273673958119858729226349232 := by
  rw [← show ((([(53, 1), (1151792954303, 1), (3060006329088659, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_53, prime_oneHundredFiftyEightEZ_1151792954303, prime_oneHundredFiftyEightEZ_3060006329088659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132882 : Nat.totient 186798167688245943546795132882 = 62101095207454931847165039744 := by
  rw [← show ((([(2, 1), (3, 2), (379, 1), (93557, 1), (9527149, 1), (30720031178467, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_379, prime_oneHundredFiftyEightEZ_93557, prime_oneHundredFiftyEightEZ_9527149, prime_oneHundredFiftyEightEZ_30720031178467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132883 : Nat.totient 186798167688245943546795132883 = 186798167688245943546795132882 := by
  rw [← show ((([(186798167688245943546795132883, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_186798167688245943546795132883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132884 : Nat.totient 186798167688245943546795132884 = 93398928163674654150543830400 := by
  rw [← show ((([(2, 2), (599941, 1), (77840224158811426268081, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_599941, prime_oneHundredFiftyEightEZ_77840224158811426268081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132885 : Nat.totient 186798167688245943546795132885 = 99625689433731169891624070864 := by
  rw [← show ((([(3, 1), (5, 1), (12453211179216396236453008859, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_12453211179216396236453008859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132886 : Nat.totient 186798167688245943546795132886 = 78860485702813867553470394880 := by
  rw [← show ((([(2, 1), (13, 1), (19, 1), (29, 1), (13039101472026102439396561, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_13, prime_oneHundredFiftyEightEZ_19, prime_oneHundredFiftyEightEZ_29, prime_oneHundredFiftyEightEZ_13039101472026102439396561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132887 : Nat.totient 186798167688245943546795132887 = 159897852336275962527594780288 := by
  rw [← show ((([(7, 1), (919, 1), (3943, 1), (2301119, 1), (46457093, 1), (68887619, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_919, prime_oneHundredFiftyEightEZ_3943, prime_oneHundredFiftyEightEZ_2301119, prime_oneHundredFiftyEightEZ_46457093, prime_oneHundredFiftyEightEZ_68887619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132888 : Nat.totient 186798167688245943546795132888 = 61959900678712118709027803136 := by
  rw [← show ((([(2, 3), (3, 1), (269, 1), (883, 1), (14489, 1), (407893, 1), (5544517031803, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_269, prime_oneHundredFiftyEightEZ_883, prime_oneHundredFiftyEightEZ_14489, prime_oneHundredFiftyEightEZ_407893, prime_oneHundredFiftyEightEZ_5544517031803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132889 : Nat.totient 186798167688245943546795132889 = 186798167688245943546795132888 := by
  rw [← show ((([(186798167688245943546795132889, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_186798167688245943546795132889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132890 : Nat.totient 186798167688245943546795132890 = 67926606432089434017016411920 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (1698165160802235850425410299, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_11, prime_oneHundredFiftyEightEZ_1698165160802235850425410299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132891 : Nat.totient 186798167688245943546795132891 = 124493106383798510088949248000 := by
  rw [← show ((([(3, 2), (4349, 1), (24001, 1), (24019, 1), (8278591165857829, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_4349, prime_oneHundredFiftyEightEZ_24001, prime_oneHundredFiftyEightEZ_24019, prime_oneHundredFiftyEightEZ_8278591165857829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132892 : Nat.totient 186798167688245943546795132892 = 93398412652248352592752818672 := by
  rw [← show ((([(2, 2), (261467, 1), (297467, 1), (600422478739871407, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_261467, prime_oneHundredFiftyEightEZ_297467, prime_oneHundredFiftyEightEZ_600422478739871407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132893 : Nat.totient 186798167688245943546795132893 = 186635875619878676886715513200 := by
  rw [← show ((([(1151, 1), (71549123839, 1), (2268260700492637, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_1151, prime_oneHundredFiftyEightEZ_71549123839, prime_oneHundredFiftyEightEZ_2268260700492637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132894 : Nat.totient 186798167688245943546795132894 = 53358599103136219432453017600 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (4337, 1), (80075433121, 1), (12806622349891, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_4337, prime_oneHundredFiftyEightEZ_80075433121, prime_oneHundredFiftyEightEZ_12806622349891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132895 : Nat.totient 186798167688245943546795132895 = 139835037736294549239246559744 := by
  rw [← show ((([(5, 1), (17, 1), (173, 1), (12703037585055827510832719, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_17, prime_oneHundredFiftyEightEZ_173, prime_oneHundredFiftyEightEZ_12703037585055827510832719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132896 : Nat.totient 186798167688245943546795132896 = 91098350940570308146052275200 := by
  rw [← show ((([(2, 5), (41, 1), (4013, 1), (35478856765862688553891, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_41, prime_oneHundredFiftyEightEZ_4013, prime_oneHundredFiftyEightEZ_35478856765862688553891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132897 : Nat.totient 186798167688245943546795132897 = 123845334664015716209928267840 := by
  rw [← show ((([(3, 1), (283, 1), (503, 1), (4680667, 1), (31633883, 1), (2954178191, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_283, prime_oneHundredFiftyEightEZ_503, prime_oneHundredFiftyEightEZ_4680667, prime_oneHundredFiftyEightEZ_31633883, prime_oneHundredFiftyEightEZ_2954178191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132898 : Nat.totient 186798167688245943546795132898 = 91562206267336175809553203200 := by
  rw [← show ((([(2, 1), (97, 1), (197, 1), (229, 1), (50341, 1), (108203, 1), (179813, 1), (21791491, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_97, prime_oneHundredFiftyEightEZ_197, prime_oneHundredFiftyEightEZ_229, prime_oneHundredFiftyEightEZ_50341, prime_oneHundredFiftyEightEZ_108203, prime_oneHundredFiftyEightEZ_179813, prime_oneHundredFiftyEightEZ_21791491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132899 : Nat.totient 186798167688245943546795132899 = 172429077866068418644318973760 := by
  rw [← show ((([(13, 1), (40323620939753, 1), (356344234155991, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_13, prime_oneHundredFiftyEightEZ_40323620939753, prime_oneHundredFiftyEightEZ_356344234155991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132900 : Nat.totient 186798167688245943546795132900 = 49762661578441880592248524800 := by
  rw [← show ((([(2, 2), (3, 4), (5, 2), (1013, 1), (49307, 1), (185272081, 1), (2492066279, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_2, prime_oneHundredFiftyEightEZ_3, prime_oneHundredFiftyEightEZ_5, prime_oneHundredFiftyEightEZ_1013, prime_oneHundredFiftyEightEZ_49307, prime_oneHundredFiftyEightEZ_185272081, prime_oneHundredFiftyEightEZ_2492066279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyEightEZ_186798167688245943546795132901 : Nat.totient 186798167688245943546795132901 = 134735314295778614535880224000 := by
  rw [← show ((([(7, 2), (11, 1), (23, 1), (31, 1), (71161, 1), (6830496520238248063, 1)] : List FactorBlock).map factorBlockValue).prod) = 186798167688245943546795132901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyEightEZ_7, prime_oneHundredFiftyEightEZ_11, prime_oneHundredFiftyEightEZ_23, prime_oneHundredFiftyEightEZ_31, prime_oneHundredFiftyEightEZ_71161, prime_oneHundredFiftyEightEZ_6830496520238248063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFiftyEightEZ : certifiedKill 1 186798167688245943546795132799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132800, phi_oneHundredFiftyEightEZ_186798167688245943546795132801, phi_oneHundredFiftyEightEZ_186798167688245943546795132802,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132803, phi_oneHundredFiftyEightEZ_186798167688245943546795132804, phi_oneHundredFiftyEightEZ_186798167688245943546795132805,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132806, phi_oneHundredFiftyEightEZ_186798167688245943546795132807, phi_oneHundredFiftyEightEZ_186798167688245943546795132808,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132809, phi_oneHundredFiftyEightEZ_186798167688245943546795132810, phi_oneHundredFiftyEightEZ_186798167688245943546795132811,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132812, phi_oneHundredFiftyEightEZ_186798167688245943546795132813, phi_oneHundredFiftyEightEZ_186798167688245943546795132814,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132815, phi_oneHundredFiftyEightEZ_186798167688245943546795132816, phi_oneHundredFiftyEightEZ_186798167688245943546795132817,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132818, phi_oneHundredFiftyEightEZ_186798167688245943546795132819, phi_oneHundredFiftyEightEZ_186798167688245943546795132820,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132821, phi_oneHundredFiftyEightEZ_186798167688245943546795132822, phi_oneHundredFiftyEightEZ_186798167688245943546795132823,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132824, phi_oneHundredFiftyEightEZ_186798167688245943546795132825, phi_oneHundredFiftyEightEZ_186798167688245943546795132826,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132827, phi_oneHundredFiftyEightEZ_186798167688245943546795132828, phi_oneHundredFiftyEightEZ_186798167688245943546795132829,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132830, phi_oneHundredFiftyEightEZ_186798167688245943546795132831, phi_oneHundredFiftyEightEZ_186798167688245943546795132832,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132833, phi_oneHundredFiftyEightEZ_186798167688245943546795132834, phi_oneHundredFiftyEightEZ_186798167688245943546795132835,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132836, phi_oneHundredFiftyEightEZ_186798167688245943546795132837, phi_oneHundredFiftyEightEZ_186798167688245943546795132838,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132839, phi_oneHundredFiftyEightEZ_186798167688245943546795132840, phi_oneHundredFiftyEightEZ_186798167688245943546795132841,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132842, phi_oneHundredFiftyEightEZ_186798167688245943546795132843, phi_oneHundredFiftyEightEZ_186798167688245943546795132844,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132845, phi_oneHundredFiftyEightEZ_186798167688245943546795132846, phi_oneHundredFiftyEightEZ_186798167688245943546795132847,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132848, phi_oneHundredFiftyEightEZ_186798167688245943546795132849, phi_oneHundredFiftyEightEZ_186798167688245943546795132850,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132851, phi_oneHundredFiftyEightEZ_186798167688245943546795132852, phi_oneHundredFiftyEightEZ_186798167688245943546795132853,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132854, phi_oneHundredFiftyEightEZ_186798167688245943546795132855, phi_oneHundredFiftyEightEZ_186798167688245943546795132856,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132857, phi_oneHundredFiftyEightEZ_186798167688245943546795132858, phi_oneHundredFiftyEightEZ_186798167688245943546795132859,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132860, phi_oneHundredFiftyEightEZ_186798167688245943546795132861, phi_oneHundredFiftyEightEZ_186798167688245943546795132862,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132863, phi_oneHundredFiftyEightEZ_186798167688245943546795132864, phi_oneHundredFiftyEightEZ_186798167688245943546795132865,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132866, phi_oneHundredFiftyEightEZ_186798167688245943546795132867, phi_oneHundredFiftyEightEZ_186798167688245943546795132868,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132869, phi_oneHundredFiftyEightEZ_186798167688245943546795132870, phi_oneHundredFiftyEightEZ_186798167688245943546795132871,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132872, phi_oneHundredFiftyEightEZ_186798167688245943546795132873, phi_oneHundredFiftyEightEZ_186798167688245943546795132874,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132875, phi_oneHundredFiftyEightEZ_186798167688245943546795132876, phi_oneHundredFiftyEightEZ_186798167688245943546795132877,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132878, phi_oneHundredFiftyEightEZ_186798167688245943546795132879, phi_oneHundredFiftyEightEZ_186798167688245943546795132880,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132881, phi_oneHundredFiftyEightEZ_186798167688245943546795132882, phi_oneHundredFiftyEightEZ_186798167688245943546795132883,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132884, phi_oneHundredFiftyEightEZ_186798167688245943546795132885, phi_oneHundredFiftyEightEZ_186798167688245943546795132886,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132887, phi_oneHundredFiftyEightEZ_186798167688245943546795132888, phi_oneHundredFiftyEightEZ_186798167688245943546795132889,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132890, phi_oneHundredFiftyEightEZ_186798167688245943546795132891, phi_oneHundredFiftyEightEZ_186798167688245943546795132892,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132893, phi_oneHundredFiftyEightEZ_186798167688245943546795132894, phi_oneHundredFiftyEightEZ_186798167688245943546795132895,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132896, phi_oneHundredFiftyEightEZ_186798167688245943546795132897, phi_oneHundredFiftyEightEZ_186798167688245943546795132898,
    phi_oneHundredFiftyEightEZ_186798167688245943546795132899, phi_oneHundredFiftyEightEZ_186798167688245943546795132900, phi_oneHundredFiftyEightEZ_186798167688245943546795132901]

end TotientTailPeriodKiller
end Erdos249257
