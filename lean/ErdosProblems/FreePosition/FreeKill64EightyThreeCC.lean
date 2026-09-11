import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def eightyThreeCCFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem eightyThreeCCFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : eightyThreeCCFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [eightyThreeCCFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [eightyThreeCCFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then eightyThreeCCFastPow a n * eightyThreeCCFastPow a n * a else eightyThreeCCFastPow a n * eightyThreeCCFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_eightyThreeCC_2 : Nat.Prime 2 := by norm_num

private theorem prime_eightyThreeCC_3 : Nat.Prime 3 := by norm_num

private theorem prime_eightyThreeCC_5 : Nat.Prime 5 := by norm_num

private theorem prime_eightyThreeCC_7 : Nat.Prime 7 := by norm_num

private theorem prime_eightyThreeCC_11 : Nat.Prime 11 := by norm_num

private theorem prime_eightyThreeCC_13 : Nat.Prime 13 := by norm_num

private theorem prime_eightyThreeCC_17 : Nat.Prime 17 := by norm_num

private theorem prime_eightyThreeCC_19 : Nat.Prime 19 := by norm_num

private theorem prime_eightyThreeCC_23 : Nat.Prime 23 := by norm_num

private theorem prime_eightyThreeCC_29 : Nat.Prime 29 := by norm_num

private theorem prime_eightyThreeCC_31 : Nat.Prime 31 := by norm_num

private theorem prime_eightyThreeCC_37 : Nat.Prime 37 := by norm_num

private theorem prime_eightyThreeCC_41 : Nat.Prime 41 := by norm_num

private theorem prime_eightyThreeCC_43 : Nat.Prime 43 := by norm_num

private theorem prime_eightyThreeCC_47 : Nat.Prime 47 := by norm_num

private theorem prime_eightyThreeCC_53 : Nat.Prime 53 := by norm_num

private theorem prime_eightyThreeCC_59 : Nat.Prime 59 := by norm_num

private theorem prime_eightyThreeCC_61 : Nat.Prime 61 := by norm_num

private theorem prime_eightyThreeCC_67 : Nat.Prime 67 := by norm_num

private theorem prime_eightyThreeCC_71 : Nat.Prime 71 := by norm_num

private theorem prime_eightyThreeCC_73 : Nat.Prime 73 := by norm_num

private theorem prime_eightyThreeCC_79 : Nat.Prime 79 := by norm_num

private theorem prime_eightyThreeCC_83 : Nat.Prime 83 := by norm_num

private theorem prime_eightyThreeCC_89 : Nat.Prime 89 := by norm_num

private theorem prime_eightyThreeCC_97 : Nat.Prime 97 := by norm_num

private theorem prime_eightyThreeCC_101 : Nat.Prime 101 := by norm_num

private theorem prime_eightyThreeCC_103 : Nat.Prime 103 := by norm_num

private theorem prime_eightyThreeCC_107 : Nat.Prime 107 := by norm_num

private theorem prime_eightyThreeCC_109 : Nat.Prime 109 := by norm_num

private theorem prime_eightyThreeCC_113 : Nat.Prime 113 := by norm_num

private theorem prime_eightyThreeCC_127 : Nat.Prime 127 := by norm_num

private theorem prime_eightyThreeCC_131 : Nat.Prime 131 := by norm_num

private theorem prime_eightyThreeCC_137 : Nat.Prime 137 := by norm_num

private theorem prime_eightyThreeCC_139 : Nat.Prime 139 := by norm_num

private theorem prime_eightyThreeCC_149 : Nat.Prime 149 := by norm_num

private theorem prime_eightyThreeCC_151 : Nat.Prime 151 := by norm_num

private theorem prime_eightyThreeCC_157 : Nat.Prime 157 := by norm_num

private theorem prime_eightyThreeCC_163 : Nat.Prime 163 := by norm_num

private theorem prime_eightyThreeCC_167 : Nat.Prime 167 := by norm_num

private theorem prime_eightyThreeCC_173 : Nat.Prime 173 := by norm_num

private theorem prime_eightyThreeCC_181 : Nat.Prime 181 := by norm_num

private theorem prime_eightyThreeCC_191 : Nat.Prime 191 := by norm_num

private theorem prime_eightyThreeCC_193 : Nat.Prime 193 := by norm_num

private theorem prime_eightyThreeCC_199 : Nat.Prime 199 := by norm_num

private theorem prime_eightyThreeCC_211 : Nat.Prime 211 := by norm_num

private theorem prime_eightyThreeCC_223 : Nat.Prime 223 := by norm_num

private theorem prime_eightyThreeCC_227 : Nat.Prime 227 := by norm_num

private theorem prime_eightyThreeCC_241 : Nat.Prime 241 := by norm_num

private theorem prime_eightyThreeCC_251 : Nat.Prime 251 := by norm_num

private theorem prime_eightyThreeCC_257 : Nat.Prime 257 := by norm_num

private theorem prime_eightyThreeCC_263 : Nat.Prime 263 := by norm_num

private theorem prime_eightyThreeCC_269 : Nat.Prime 269 := by norm_num

private theorem prime_eightyThreeCC_271 : Nat.Prime 271 := by norm_num

private theorem prime_eightyThreeCC_277 : Nat.Prime 277 := by norm_num

private theorem prime_eightyThreeCC_307 : Nat.Prime 307 := by norm_num

private theorem prime_eightyThreeCC_311 : Nat.Prime 311 := by norm_num

private theorem prime_eightyThreeCC_317 : Nat.Prime 317 := by norm_num

private theorem prime_eightyThreeCC_331 : Nat.Prime 331 := by norm_num

private theorem prime_eightyThreeCC_337 : Nat.Prime 337 := by norm_num

private theorem prime_eightyThreeCC_347 : Nat.Prime 347 := by norm_num

private theorem prime_eightyThreeCC_349 : Nat.Prime 349 := by norm_num

private theorem prime_eightyThreeCC_353 : Nat.Prime 353 := by norm_num

private theorem prime_eightyThreeCC_367 : Nat.Prime 367 := by norm_num

private theorem prime_eightyThreeCC_373 : Nat.Prime 373 := by norm_num

private theorem prime_eightyThreeCC_383 : Nat.Prime 383 := by norm_num

private theorem prime_eightyThreeCC_397 : Nat.Prime 397 := by norm_num

private theorem prime_eightyThreeCC_421 : Nat.Prime 421 := by norm_num

private theorem prime_eightyThreeCC_439 : Nat.Prime 439 := by norm_num

private theorem prime_eightyThreeCC_443 : Nat.Prime 443 := by norm_num

private theorem prime_eightyThreeCC_449 : Nat.Prime 449 := by norm_num

private theorem prime_eightyThreeCC_457 : Nat.Prime 457 := by norm_num

private theorem prime_eightyThreeCC_461 : Nat.Prime 461 := by norm_num

private theorem prime_eightyThreeCC_467 : Nat.Prime 467 := by norm_num

private theorem prime_eightyThreeCC_479 : Nat.Prime 479 := by norm_num

private theorem prime_eightyThreeCC_491 : Nat.Prime 491 := by norm_num

private theorem prime_eightyThreeCC_499 : Nat.Prime 499 := by norm_num

private theorem prime_eightyThreeCC_503 : Nat.Prime 503 := by norm_num

private theorem prime_eightyThreeCC_521 : Nat.Prime 521 := by norm_num

private theorem prime_eightyThreeCC_523 : Nat.Prime 523 := by norm_num

private theorem prime_eightyThreeCC_547 : Nat.Prime 547 := by norm_num

private theorem prime_eightyThreeCC_571 : Nat.Prime 571 := by norm_num

private theorem prime_eightyThreeCC_577 : Nat.Prime 577 := by norm_num

private theorem prime_eightyThreeCC_587 : Nat.Prime 587 := by norm_num

private theorem prime_eightyThreeCC_607 : Nat.Prime 607 := by norm_num

private theorem prime_eightyThreeCC_613 : Nat.Prime 613 := by norm_num

private theorem prime_eightyThreeCC_617 : Nat.Prime 617 := by norm_num

private theorem prime_eightyThreeCC_631 : Nat.Prime 631 := by norm_num

private theorem prime_eightyThreeCC_641 : Nat.Prime 641 := by norm_num

private theorem prime_eightyThreeCC_643 : Nat.Prime 643 := by norm_num

private theorem prime_eightyThreeCC_647 : Nat.Prime 647 := by norm_num

private theorem prime_eightyThreeCC_659 : Nat.Prime 659 := by norm_num

private theorem prime_eightyThreeCC_661 : Nat.Prime 661 := by norm_num

private theorem prime_eightyThreeCC_677 : Nat.Prime 677 := by norm_num

private theorem prime_eightyThreeCC_683 : Nat.Prime 683 := by norm_num

private theorem prime_eightyThreeCC_727 : Nat.Prime 727 := by norm_num

private theorem prime_eightyThreeCC_733 : Nat.Prime 733 := by norm_num

private theorem prime_eightyThreeCC_743 : Nat.Prime 743 := by norm_num

private theorem prime_eightyThreeCC_751 : Nat.Prime 751 := by norm_num

private theorem prime_eightyThreeCC_761 : Nat.Prime 761 := by norm_num

private theorem prime_eightyThreeCC_797 : Nat.Prime 797 := by norm_num

private theorem prime_eightyThreeCC_811 : Nat.Prime 811 := by norm_num

private theorem prime_eightyThreeCC_821 : Nat.Prime 821 := by norm_num

private theorem prime_eightyThreeCC_829 : Nat.Prime 829 := by norm_num

private theorem prime_eightyThreeCC_857 : Nat.Prime 857 := by norm_num

private theorem prime_eightyThreeCC_859 : Nat.Prime 859 := by norm_num

private theorem prime_eightyThreeCC_877 : Nat.Prime 877 := by norm_num

private theorem prime_eightyThreeCC_881 : Nat.Prime 881 := by norm_num

private theorem prime_eightyThreeCC_907 : Nat.Prime 907 := by norm_num

private theorem prime_eightyThreeCC_919 : Nat.Prime 919 := by norm_num

private theorem prime_eightyThreeCC_947 : Nat.Prime 947 := by norm_num

private theorem prime_eightyThreeCC_953 : Nat.Prime 953 := by norm_num

private theorem prime_eightyThreeCC_991 : Nat.Prime 991 := by norm_num

private theorem prime_eightyThreeCC_997 : Nat.Prime 997 := by norm_num

private theorem prime_eightyThreeCC_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_eightyThreeCC_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_eightyThreeCC_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_eightyThreeCC_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_eightyThreeCC_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_eightyThreeCC_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_eightyThreeCC_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_eightyThreeCC_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_eightyThreeCC_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_eightyThreeCC_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_eightyThreeCC_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_eightyThreeCC_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_eightyThreeCC_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_eightyThreeCC_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_eightyThreeCC_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_eightyThreeCC_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_eightyThreeCC_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_eightyThreeCC_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_eightyThreeCC_1613 : Nat.Prime 1613 := by norm_num

private theorem prime_eightyThreeCC_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_eightyThreeCC_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_eightyThreeCC_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_eightyThreeCC_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_eightyThreeCC_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_eightyThreeCC_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_eightyThreeCC_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_eightyThreeCC_1801 : Nat.Prime 1801 := by norm_num

private theorem prime_eightyThreeCC_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_eightyThreeCC_1913 : Nat.Prime 1913 := by norm_num

private theorem prime_eightyThreeCC_1949 : Nat.Prime 1949 := by norm_num

private theorem prime_eightyThreeCC_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_eightyThreeCC_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_eightyThreeCC_2017 : Nat.Prime 2017 := by norm_num

private theorem prime_eightyThreeCC_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_eightyThreeCC_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_eightyThreeCC_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_eightyThreeCC_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_eightyThreeCC_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_eightyThreeCC_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_eightyThreeCC_2293 : Nat.Prime 2293 := by norm_num

private theorem prime_eightyThreeCC_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_eightyThreeCC_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_eightyThreeCC_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_eightyThreeCC_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_eightyThreeCC_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_eightyThreeCC_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_eightyThreeCC_2531 : Nat.Prime 2531 := by norm_num

private theorem prime_eightyThreeCC_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_eightyThreeCC_2549 : Nat.Prime 2549 := by norm_num

private theorem prime_eightyThreeCC_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_eightyThreeCC_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_eightyThreeCC_2713 : Nat.Prime 2713 := by norm_num

private theorem prime_eightyThreeCC_2719 : Nat.Prime 2719 := by norm_num

private theorem prime_eightyThreeCC_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_eightyThreeCC_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_eightyThreeCC_3037 : Nat.Prime 3037 := by norm_num

private theorem prime_eightyThreeCC_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_eightyThreeCC_3299 : Nat.Prime 3299 := by norm_num

private theorem prime_eightyThreeCC_3323 : Nat.Prime 3323 := by norm_num

private theorem prime_eightyThreeCC_3407 : Nat.Prime 3407 := by norm_num

private theorem prime_eightyThreeCC_3457 : Nat.Prime 3457 := by norm_num

private theorem prime_eightyThreeCC_3517 : Nat.Prime 3517 := by norm_num

private theorem prime_eightyThreeCC_3539 : Nat.Prime 3539 := by norm_num

private theorem prime_eightyThreeCC_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_eightyThreeCC_3613 : Nat.Prime 3613 := by norm_num

private theorem prime_eightyThreeCC_3677 : Nat.Prime 3677 := by norm_num

private theorem prime_eightyThreeCC_3709 : Nat.Prime 3709 := by norm_num

private theorem prime_eightyThreeCC_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_eightyThreeCC_3821 : Nat.Prime 3821 := by norm_num

private theorem prime_eightyThreeCC_3823 : Nat.Prime 3823 := by norm_num

private theorem prime_eightyThreeCC_3863 : Nat.Prime 3863 := by norm_num

private theorem prime_eightyThreeCC_3907 : Nat.Prime 3907 := by norm_num

private theorem prime_eightyThreeCC_4013 : Nat.Prime 4013 := by norm_num

private theorem prime_eightyThreeCC_4157 : Nat.Prime 4157 := by norm_num

private theorem prime_eightyThreeCC_4241 : Nat.Prime 4241 := by norm_num

private theorem prime_eightyThreeCC_4283 : Nat.Prime 4283 := by norm_num

private theorem prime_eightyThreeCC_4357 : Nat.Prime 4357 := by norm_num

private theorem prime_eightyThreeCC_4373 : Nat.Prime 4373 := by norm_num

private theorem prime_eightyThreeCC_4391 : Nat.Prime 4391 := by norm_num

private theorem prime_eightyThreeCC_4519 : Nat.Prime 4519 := by norm_num

private theorem prime_eightyThreeCC_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_eightyThreeCC_4679 : Nat.Prime 4679 := by norm_num

private theorem prime_eightyThreeCC_4783 : Nat.Prime 4783 := by norm_num

private theorem prime_eightyThreeCC_4933 : Nat.Prime 4933 := by norm_num

private theorem prime_eightyThreeCC_5197 : Nat.Prime 5197 := by norm_num

private theorem prime_eightyThreeCC_5231 : Nat.Prime 5231 := by norm_num

private theorem prime_eightyThreeCC_5407 : Nat.Prime 5407 := by norm_num

private theorem prime_eightyThreeCC_5779 : Nat.Prime 5779 := by norm_num

private theorem prime_eightyThreeCC_6047 : Nat.Prime 6047 := by norm_num

private theorem prime_eightyThreeCC_6287 : Nat.Prime 6287 := by norm_num

private theorem prime_eightyThreeCC_6311 : Nat.Prime 6311 := by norm_num

private theorem prime_eightyThreeCC_6491 : Nat.Prime 6491 := by norm_num

private theorem prime_eightyThreeCC_6521 : Nat.Prime 6521 := by norm_num

private theorem prime_eightyThreeCC_6983 : Nat.Prime 6983 := by norm_num

private theorem prime_eightyThreeCC_7213 : Nat.Prime 7213 := by norm_num

private theorem prime_eightyThreeCC_7369 : Nat.Prime 7369 := by norm_num

private theorem prime_eightyThreeCC_7541 : Nat.Prime 7541 := by norm_num

private theorem prime_eightyThreeCC_7759 : Nat.Prime 7759 := by norm_num

private theorem prime_eightyThreeCC_7919 : Nat.Prime 7919 := by norm_num

private theorem prime_eightyThreeCC_8179 : Nat.Prime 8179 := by norm_num

private theorem prime_eightyThreeCC_8543 : Nat.Prime 8543 := by norm_num

private theorem prime_eightyThreeCC_8819 : Nat.Prime 8819 := by norm_num

private theorem prime_eightyThreeCC_8923 : Nat.Prime 8923 := by norm_num

private theorem prime_eightyThreeCC_9173 : Nat.Prime 9173 := by norm_num

private theorem prime_eightyThreeCC_9967 : Nat.Prime 9967 := by norm_num

private theorem prime_eightyThreeCC_10111 : Nat.Prime 10111 := by norm_num

private theorem prime_eightyThreeCC_10657 : Nat.Prime 10657 := by norm_num

private theorem prime_eightyThreeCC_10781 : Nat.Prime 10781 := by norm_num

private theorem prime_eightyThreeCC_11197 : Nat.Prime 11197 := by norm_num

private theorem prime_eightyThreeCC_11317 : Nat.Prime 11317 := by norm_num

private theorem prime_eightyThreeCC_11393 : Nat.Prime 11393 := by norm_num

private theorem prime_eightyThreeCC_11411 : Nat.Prime 11411 := by norm_num

private theorem prime_eightyThreeCC_11953 : Nat.Prime 11953 := by norm_num

private theorem prime_eightyThreeCC_12227 : Nat.Prime 12227 := by norm_num

private theorem prime_eightyThreeCC_12781 : Nat.Prime 12781 := by norm_num

private theorem prime_eightyThreeCC_12959 : Nat.Prime 12959 := by norm_num

private theorem prime_eightyThreeCC_13177 : Nat.Prime 13177 := by norm_num

private theorem prime_eightyThreeCC_13537 : Nat.Prime 13537 := by norm_num

private theorem prime_eightyThreeCC_13687 : Nat.Prime 13687 := by norm_num

private theorem prime_eightyThreeCC_14489 : Nat.Prime 14489 := by norm_num

private theorem prime_eightyThreeCC_14551 : Nat.Prime 14551 := by norm_num

private theorem prime_eightyThreeCC_14717 : Nat.Prime 14717 := by norm_num

private theorem prime_eightyThreeCC_14797 : Nat.Prime 14797 := by norm_num

private theorem prime_eightyThreeCC_14869 : Nat.Prime 14869 := by norm_num

private theorem prime_eightyThreeCC_15349 : Nat.Prime 15349 := by norm_num

private theorem prime_eightyThreeCC_15817 : Nat.Prime 15817 := by norm_num

private theorem prime_eightyThreeCC_16193 : Nat.Prime 16193 := by norm_num

private theorem prime_eightyThreeCC_16267 : Nat.Prime 16267 := by norm_num

private theorem prime_eightyThreeCC_16369 : Nat.Prime 16369 := by norm_num

private theorem prime_eightyThreeCC_16411 : Nat.Prime 16411 := by norm_num

private theorem prime_eightyThreeCC_16453 : Nat.Prime 16453 := by norm_num

private theorem prime_eightyThreeCC_17377 : Nat.Prime 17377 := by norm_num

private theorem prime_eightyThreeCC_17581 : Nat.Prime 17581 := by norm_num

private theorem prime_eightyThreeCC_17761 : Nat.Prime 17761 := by norm_num

private theorem prime_eightyThreeCC_18899 : Nat.Prime 18899 := by norm_num

private theorem prime_eightyThreeCC_19681 : Nat.Prime 19681 := by norm_num

private theorem prime_eightyThreeCC_20627 : Nat.Prime 20627 := by norm_num

private theorem prime_eightyThreeCC_20771 : Nat.Prime 20771 := by norm_num

private theorem prime_eightyThreeCC_21383 : Nat.Prime 21383 := by norm_num

private theorem prime_eightyThreeCC_21521 : Nat.Prime 21521 := by norm_num

private theorem prime_eightyThreeCC_22067 : Nat.Prime 22067 := by norm_num

private theorem prime_eightyThreeCC_22109 : Nat.Prime 22109 := by norm_num

private theorem prime_eightyThreeCC_22937 : Nat.Prime 22937 := by norm_num

private theorem prime_eightyThreeCC_23531 : Nat.Prime 23531 := by norm_num

private theorem prime_eightyThreeCC_24763 : Nat.Prime 24763 := by norm_num

private theorem prime_eightyThreeCC_25339 : Nat.Prime 25339 := by norm_num

private theorem prime_eightyThreeCC_25439 : Nat.Prime 25439 := by norm_num

private theorem prime_eightyThreeCC_26177 : Nat.Prime 26177 := by norm_num

private theorem prime_eightyThreeCC_26699 : Nat.Prime 26699 := by norm_num

private theorem prime_eightyThreeCC_27893 : Nat.Prime 27893 := by norm_num

private theorem prime_eightyThreeCC_29759 : Nat.Prime 29759 := by norm_num

private theorem prime_eightyThreeCC_30367 : Nat.Prime 30367 := by norm_num

private theorem prime_eightyThreeCC_30911 : Nat.Prime 30911 := by norm_num

private theorem prime_eightyThreeCC_32237 : Nat.Prime 32237 := by norm_num

private theorem prime_eightyThreeCC_32531 : Nat.Prime 32531 := by norm_num

private theorem prime_eightyThreeCC_32579 : Nat.Prime 32579 := by norm_num

private theorem prime_eightyThreeCC_32587 : Nat.Prime 32587 := by norm_num

private theorem prime_eightyThreeCC_32869 : Nat.Prime 32869 := by norm_num

private theorem prime_eightyThreeCC_32993 : Nat.Prime 32993 := by norm_num

private theorem prime_eightyThreeCC_34171 : Nat.Prime 34171 := by norm_num

private theorem prime_eightyThreeCC_34913 : Nat.Prime 34913 := by norm_num

private theorem prime_eightyThreeCC_34961 : Nat.Prime 34961 := by norm_num

private theorem prime_eightyThreeCC_35401 : Nat.Prime 35401 := by norm_num

private theorem prime_eightyThreeCC_35801 : Nat.Prime 35801 := by norm_num

private theorem prime_eightyThreeCC_37223 : Nat.Prime 37223 := by norm_num

private theorem prime_eightyThreeCC_40759 : Nat.Prime 40759 := by norm_num

private theorem prime_eightyThreeCC_40993 : Nat.Prime 40993 := by norm_num

private theorem prime_eightyThreeCC_41201 : Nat.Prime 41201 := by norm_num

private theorem prime_eightyThreeCC_42751 : Nat.Prime 42751 := by norm_num

private theorem prime_eightyThreeCC_45667 : Nat.Prime 45667 := by norm_num

private theorem prime_eightyThreeCC_45673 : Nat.Prime 45673 := by norm_num

private theorem prime_eightyThreeCC_45953 : Nat.Prime 45953 := by norm_num

private theorem prime_eightyThreeCC_46307 : Nat.Prime 46307 := by norm_num

private theorem prime_eightyThreeCC_46933 : Nat.Prime 46933 := by norm_num

private theorem prime_eightyThreeCC_47057 : Nat.Prime 47057 := by norm_num

private theorem prime_eightyThreeCC_50263 : Nat.Prime 50263 := by norm_num

private theorem prime_eightyThreeCC_50333 : Nat.Prime 50333 := by norm_num

private theorem prime_eightyThreeCC_51713 : Nat.Prime 51713 := by norm_num

private theorem prime_eightyThreeCC_52223 : Nat.Prime 52223 := by norm_num

private theorem prime_eightyThreeCC_54323 : Nat.Prime 54323 := by norm_num

private theorem prime_eightyThreeCC_59053 : Nat.Prime 59053 := by norm_num

private theorem prime_eightyThreeCC_59377 : Nat.Prime 59377 := by norm_num

private theorem prime_eightyThreeCC_61051 : Nat.Prime 61051 := by norm_num

private theorem prime_eightyThreeCC_67049 : Nat.Prime 67049 := by norm_num

private theorem prime_eightyThreeCC_69389 : Nat.Prime 69389 := by norm_num

private theorem prime_eightyThreeCC_76423 : Nat.Prime 76423 := by norm_num

private theorem prime_eightyThreeCC_80317 : Nat.Prime 80317 := by norm_num

private theorem prime_eightyThreeCC_83219 : Nat.Prime 83219 := by norm_num

private theorem prime_eightyThreeCC_83689 : Nat.Prime 83689 := by norm_num

private theorem prime_eightyThreeCC_83813 : Nat.Prime 83813 := by norm_num

private theorem prime_eightyThreeCC_96263 : Nat.Prime 96263 := by norm_num

private theorem prime_eightyThreeCC_96353 : Nat.Prime 96353 := by norm_num

private theorem prime_eightyThreeCC_104917 : Nat.Prime 104917 := by norm_num

private theorem prime_eightyThreeCC_110311 : Nat.Prime 110311 := by norm_num

private theorem prime_eightyThreeCC_111347 : Nat.Prime 111347 := by norm_num

private theorem prime_eightyThreeCC_112303 : Nat.Prime 112303 := by norm_num

private theorem prime_eightyThreeCC_114479 : Nat.Prime 114479 := by norm_num

private theorem prime_eightyThreeCC_116189 : Nat.Prime 116189 := by norm_num

private theorem prime_eightyThreeCC_116639 : Nat.Prime 116639 := by norm_num

private theorem prime_eightyThreeCC_118687 : Nat.Prime 118687 := by norm_num

private theorem prime_eightyThreeCC_119359 : Nat.Prime 119359 := by norm_num

private theorem prime_eightyThreeCC_123491 : Nat.Prime 123491 := by norm_num

private theorem prime_eightyThreeCC_127493 : Nat.Prime 127493 := by norm_num

private theorem prime_eightyThreeCC_132313 : Nat.Prime 132313 := by norm_num

private theorem prime_eightyThreeCC_134581 : Nat.Prime 134581 := by norm_num

private theorem prime_eightyThreeCC_140177 : Nat.Prime 140177 := by norm_num

private theorem prime_eightyThreeCC_150401 : Nat.Prime 150401 := by norm_num

private theorem prime_eightyThreeCC_165211 : Nat.Prime 165211 := by norm_num

private theorem prime_eightyThreeCC_180883 : Nat.Prime 180883 := by norm_num

private theorem prime_eightyThreeCC_181499 : Nat.Prime 181499 := by norm_num

private theorem prime_eightyThreeCC_189853 : Nat.Prime 189853 := by norm_num

private theorem prime_eightyThreeCC_194839 : Nat.Prime 194839 := by norm_num

private theorem prime_eightyThreeCC_195929 : Nat.Prime 195929 := by norm_num

private theorem prime_eightyThreeCC_206273 : Nat.Prime 206273 := by norm_num

private theorem prime_eightyThreeCC_221713 : Nat.Prime 221713 := by norm_num

private theorem prime_eightyThreeCC_239167 : Nat.Prime 239167 := by norm_num

private theorem prime_eightyThreeCC_277213 : Nat.Prime 277213 := by norm_num

private theorem prime_eightyThreeCC_291089 : Nat.Prime 291089 := by norm_num

private theorem prime_eightyThreeCC_320179 : Nat.Prime 320179 := by norm_num

private theorem prime_eightyThreeCC_336829 : Nat.Prime 336829 := by norm_num

private theorem prime_eightyThreeCC_357559 : Nat.Prime 357559 := by norm_num

private theorem prime_eightyThreeCC_359477 : Nat.Prime 359477 := by norm_num

private theorem prime_eightyThreeCC_363557 : Nat.Prime 363557 := by norm_num

private theorem prime_eightyThreeCC_376199 : Nat.Prime 376199 := by norm_num

private theorem prime_eightyThreeCC_385943 : Nat.Prime 385943 := by norm_num

private theorem prime_eightyThreeCC_389381 : Nat.Prime 389381 := by norm_num

private theorem prime_eightyThreeCC_391739 : Nat.Prime 391739 := by norm_num

private theorem prime_eightyThreeCC_393473 : Nat.Prime 393473 := by norm_num

private theorem prime_eightyThreeCC_406093 : Nat.Prime 406093 := by norm_num

private theorem prime_eightyThreeCC_439787 : Nat.Prime 439787 := by norm_num

private theorem prime_eightyThreeCC_443869 : Nat.Prime 443869 := by norm_num

private theorem prime_eightyThreeCC_452233 : Nat.Prime 452233 := by norm_num

private theorem prime_eightyThreeCC_454199 : Nat.Prime 454199 := by norm_num

private theorem prime_eightyThreeCC_460247 : Nat.Prime 460247 := by norm_num

private theorem prime_eightyThreeCC_469589 : Nat.Prime 469589 := by norm_num

private theorem prime_eightyThreeCC_487247 : Nat.Prime 487247 := by norm_num

private theorem prime_eightyThreeCC_505711 : Nat.Prime 505711 := by norm_num

private theorem prime_eightyThreeCC_546617 : Nat.Prime 546617 := by norm_num

private theorem prime_eightyThreeCC_549943 : Nat.Prime 549943 := by norm_num

private theorem prime_eightyThreeCC_550189 : Nat.Prime 550189 := by norm_num

private theorem prime_eightyThreeCC_552731 : Nat.Prime 552731 := by norm_num

private theorem prime_eightyThreeCC_556573 : Nat.Prime 556573 := by norm_num

private theorem prime_eightyThreeCC_679691 : Nat.Prime 679691 := by norm_num

private theorem prime_eightyThreeCC_754651 : Nat.Prime 754651 := by norm_num

private theorem prime_eightyThreeCC_804283 : Nat.Prime 804283 := by norm_num

private theorem prime_eightyThreeCC_823913 : Nat.Prime 823913 := by norm_num

private theorem prime_eightyThreeCC_858397 : Nat.Prime 858397 := by norm_num

private theorem prime_eightyThreeCC_865003 : Nat.Prime 865003 := by norm_num

private theorem prime_eightyThreeCC_897581 : Nat.Prime 897581 := by norm_num

private theorem prime_eightyThreeCC_974513 : Nat.Prime 974513 := by norm_num

private theorem prime_eightyThreeCC_1035893 : Nat.Prime 1035893 := by norm_num

private theorem prime_eightyThreeCC_1046597 : Nat.Prime 1046597 := by norm_num

private theorem prime_eightyThreeCC_1077371 : Nat.Prime 1077371 := by norm_num

private theorem prime_eightyThreeCC_1078159 : Nat.Prime 1078159 := by norm_num

private theorem prime_eightyThreeCC_1096163 : Nat.Prime 1096163 := by norm_num

private theorem prime_eightyThreeCC_1132567 : Nat.Prime 1132567 := by norm_num

private theorem prime_eightyThreeCC_1187941 : Nat.Prime 1187941 := by norm_num

private theorem prime_eightyThreeCC_1255663 : Nat.Prime 1255663 := by norm_num

private theorem prime_eightyThreeCC_1393261 : Nat.Prime 1393261 := by norm_num

private theorem prime_eightyThreeCC_1436363 : Nat.Prime 1436363 := by norm_num

private theorem prime_eightyThreeCC_1535531 : Nat.Prime 1535531 := by norm_num

private theorem prime_eightyThreeCC_1573021 : Nat.Prime 1573021 := by norm_num

private theorem prime_eightyThreeCC_1577119 : Nat.Prime 1577119 := by norm_num

private theorem prime_eightyThreeCC_1620973 : Nat.Prime 1620973 := by norm_num

private theorem prime_eightyThreeCC_1633679 : Nat.Prime 1633679 := by norm_num

private theorem prime_eightyThreeCC_1667881 : Nat.Prime 1667881 := by norm_num

private theorem prime_eightyThreeCC_1803457 : Nat.Prime 1803457 := by norm_num

private theorem prime_eightyThreeCC_1807361 : Nat.Prime 1807361 := by norm_num

private theorem prime_eightyThreeCC_1809271 : Nat.Prime 1809271 := by norm_num

private theorem prime_eightyThreeCC_1813277 : Nat.Prime 1813277 := by norm_num

private theorem prime_eightyThreeCC_1959943 : Nat.Prime 1959943 := by norm_num

private theorem prime_eightyThreeCC_2030081 : Nat.Prime 2030081 := by norm_num

private theorem prime_eightyThreeCC_2236781 : Nat.Prime 2236781 := by norm_num

private theorem prime_eightyThreeCC_2366669 : Nat.Prime 2366669 := by norm_num

private theorem prime_eightyThreeCC_2488427 : Nat.Prime 2488427 := by norm_num

private theorem prime_eightyThreeCC_2506291 : Nat.Prime 2506291 := by norm_num

private theorem prime_eightyThreeCC_2578573 : Nat.Prime 2578573 := by norm_num

private theorem prime_eightyThreeCC_2607929 : Nat.Prime 2607929 := by norm_num

private theorem prime_eightyThreeCC_2737169 : Nat.Prime 2737169 := by norm_num

private theorem prime_eightyThreeCC_2752403 : Nat.Prime 2752403 := by norm_num

private theorem prime_eightyThreeCC_2813339 : Nat.Prime 2813339 := by norm_num

private theorem prime_eightyThreeCC_2829569 : Nat.Prime 2829569 := by norm_num

private theorem prime_eightyThreeCC_2858467 : Nat.Prime 2858467 := by norm_num

private theorem prime_eightyThreeCC_2928749 : Nat.Prime 2928749 := by norm_num

private theorem prime_eightyThreeCC_3063217 : Nat.Prime 3063217 := by norm_num

private theorem prime_eightyThreeCC_3193559 : Nat.Prime 3193559 := by norm_num

private theorem prime_eightyThreeCC_3281461 : Nat.Prime 3281461 := by norm_num

private theorem prime_eightyThreeCC_3764227 : Nat.Prime 3764227 := by norm_num

private theorem prime_eightyThreeCC_3767219 : Nat.Prime 3767219 := by norm_num

private theorem prime_eightyThreeCC_3952601 : Nat.Prime 3952601 := by norm_num

private theorem prime_eightyThreeCC_3996361 : Nat.Prime 3996361 := by norm_num

private theorem prime_eightyThreeCC_4157623 : Nat.Prime 4157623 := by norm_num

private theorem prime_eightyThreeCC_4418941 : Nat.Prime 4418941 := by norm_num

private theorem prime_eightyThreeCC_4781057 : Nat.Prime 4781057 := by norm_num

private theorem prime_eightyThreeCC_5215403 : Nat.Prime 5215403 := by norm_num

private theorem prime_eightyThreeCC_5345953 : Nat.Prime 5345953 := by norm_num

private theorem prime_eightyThreeCC_5444401 : Nat.Prime 5444401 := by norm_num

private theorem prime_eightyThreeCC_5566397 : Nat.Prime 5566397 := by norm_num

private theorem prime_eightyThreeCC_5861929 : Nat.Prime 5861929 := by norm_num

private theorem prime_eightyThreeCC_6168779 : Nat.Prime 6168779 := by norm_num

private theorem prime_eightyThreeCC_6287599 : Nat.Prime 6287599 := by norm_num

private theorem prime_eightyThreeCC_6602683 : Nat.Prime 6602683 := by norm_num

private theorem prime_eightyThreeCC_6845087 : Nat.Prime 6845087 := by norm_num

private theorem prime_eightyThreeCC_7252027 : Nat.Prime 7252027 := by norm_num

private theorem prime_eightyThreeCC_7513973 : Nat.Prime 7513973 := by norm_num

private theorem prime_eightyThreeCC_8174329 : Nat.Prime 8174329 := by norm_num

private theorem prime_eightyThreeCC_8605153 : Nat.Prime 8605153 := by norm_num

private theorem prime_eightyThreeCC_8730283 : Nat.Prime 8730283 := by norm_num

private theorem prime_eightyThreeCC_8775409 : Nat.Prime 8775409 := by norm_num

private theorem prime_eightyThreeCC_9032753 : Nat.Prime 9032753 := by norm_num

private theorem prime_eightyThreeCC_10524929 : Nat.Prime 10524929 := by norm_num

private theorem prime_eightyThreeCC_12293791 : Nat.Prime 12293791 := by norm_num

private theorem prime_eightyThreeCC_14026049 : Nat.Prime 14026049 := by norm_num

private theorem prime_eightyThreeCC_14037967 : Nat.Prime 14037967 := by norm_num

private theorem prime_eightyThreeCC_14262683 : Nat.Prime 14262683 := by norm_num

private theorem prime_eightyThreeCC_15232367 : Nat.Prime 15232367 := by norm_num

private theorem prime_eightyThreeCC_15273529 : Nat.Prime 15273529 := by norm_num

private theorem prime_eightyThreeCC_16518037 : Nat.Prime 16518037 := by norm_num

private theorem prime_eightyThreeCC_17252111 : Nat.Prime 17252111 := by norm_num

private theorem prime_eightyThreeCC_17617849 : Nat.Prime 17617849 := by norm_num

private theorem prime_eightyThreeCC_18077779 : Nat.Prime 18077779 := by norm_num

private theorem prime_eightyThreeCC_20219011 : Nat.Prime 20219011 := by norm_num

private theorem prime_eightyThreeCC_20691217 : Nat.Prime 20691217 := by norm_num

private theorem prime_eightyThreeCC_22189507 : Nat.Prime 22189507 := by norm_num

private theorem prime_eightyThreeCC_22217737 : Nat.Prime 22217737 := by norm_num

private theorem prime_eightyThreeCC_23727373 : Nat.Prime 23727373 := by norm_num

private theorem prime_eightyThreeCC_25291823 : Nat.Prime 25291823 := by norm_num

private theorem prime_eightyThreeCC_29383001 : Nat.Prime 29383001 := by norm_num

private theorem prime_eightyThreeCC_29611019 : Nat.Prime 29611019 := by norm_num

private theorem prime_eightyThreeCC_31600717 : Nat.Prime 31600717 := by
  apply lucas_primality 31600717 (2 : ZMod 31600717)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (376199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (376199, 1)] : List FactorBlock).map factorBlockValue).prod) = 31600717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_376199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31600717) ^ 15800358 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31600717) ^ 10533572 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31600717) ^ 4514388 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31600717) ^ 84 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_38010227 : Nat.Prime 38010227 := by
  apply lucas_primality 38010227 (2 : ZMod 38010227)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (195929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (195929, 1)] : List FactorBlock).map factorBlockValue).prod) = 38010227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_97
      · exact prime_eightyThreeCC_195929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38010227) ^ 19005113 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 38010227) ^ 391858 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 38010227) ^ 194 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_38243069 : Nat.Prime 38243069 := by
  apply lucas_primality 38243069 (2 : ZMod 38243069)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (643, 1), (14869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (643, 1), (14869, 1)] : List FactorBlock).map factorBlockValue).prod) = 38243069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_643
      · exact prime_eightyThreeCC_14869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38243069) ^ 19121534 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 38243069) ^ 59476 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 38243069) ^ 2572 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_38903411 : Nat.Prime 38903411 := by
  apply lucas_primality 38903411 (6 : ZMod 38903411)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (42751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (42751, 1)] : List FactorBlock).map factorBlockValue).prod) = 38903411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_42751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 38903411) ^ 19451705 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 38903411) ^ 7780682 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 38903411) ^ 5557630 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 38903411) ^ 2992570 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 38903411) ^ 910 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_40390367 : Nat.Prime 40390367 := by
  apply lucas_primality 40390367 (5 : ZMod 40390367)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (797, 1), (25339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (797, 1), (25339, 1)] : List FactorBlock).map factorBlockValue).prod) = 40390367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_797
      · exact prime_eightyThreeCC_25339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 40390367) ^ 20195183 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 40390367) ^ 50678 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 40390367) ^ 1594 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_40752461 : Nat.Prime 40752461 := by
  apply lucas_primality 40752461 (2 : ZMod 40752461)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (291089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (291089, 1)] : List FactorBlock).map factorBlockValue).prod) = 40752461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_291089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40752461) ^ 20376230 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 40752461) ^ 8150492 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 40752461) ^ 5821780 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 40752461) ^ 140 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_46139393 : Nat.Prime 46139393 := by
  apply lucas_primality 46139393 (3 : ZMod 46139393)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (13, 1), (1733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (13, 1), (1733, 1)] : List FactorBlock).map factorBlockValue).prod) = 46139393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_1733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 46139393) ^ 23069696 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46139393) ^ 3549184 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46139393) ^ 26624 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_51452503 : Nat.Prime 51452503 := by
  apply lucas_primality 51452503 (3 : ZMod 51452503)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (96353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (96353, 1)] : List FactorBlock).map factorBlockValue).prod) = 51452503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_89
      · exact prime_eightyThreeCC_96353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 51452503) ^ 25726251 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 51452503) ^ 17150834 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 51452503) ^ 578118 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 51452503) ^ 534 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_51630919 : Nat.Prime 51630919 := by
  apply lucas_primality 51630919 (6 : ZMod 51630919)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8605153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8605153, 1)] : List FactorBlock).map factorBlockValue).prod) = 51630919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_8605153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 51630919) ^ 25815459 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 51630919) ^ 17210306 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 51630919) ^ 6 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_52559261 : Nat.Prime 52559261 := by
  apply lucas_primality 52559261 (2 : ZMod 52559261)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (31, 1), (6521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (31, 1), (6521, 1)] : List FactorBlock).map factorBlockValue).prod) = 52559261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_31
      · exact prime_eightyThreeCC_6521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52559261) ^ 26279630 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 52559261) ^ 10511852 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 52559261) ^ 4043020 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 52559261) ^ 1695460 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 52559261) ^ 8060 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_53031023 : Nat.Prime 53031023 := by
  apply lucas_primality 53031023 (5 : ZMod 53031023)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1009, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1009, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) = 53031023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_1009
      · exact prime_eightyThreeCC_2389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 53031023) ^ 26515511 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 53031023) ^ 4821002 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 53031023) ^ 52558 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 53031023) ^ 22198 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_53477819 : Nat.Prime 53477819 := by
  apply lucas_primality 53477819 (2 : ZMod 53477819)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 2), (4357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 2), (4357, 1)] : List FactorBlock).map factorBlockValue).prod) = 53477819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_4357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53477819) ^ 26738909 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 53477819) ^ 3145754 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 53477819) ^ 2814622 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 53477819) ^ 12274 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_59850521 : Nat.Prime 59850521 := by
  apply lucas_primality 59850521 (3 : ZMod 59850521)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (587, 1), (2549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (587, 1), (2549, 1)] : List FactorBlock).map factorBlockValue).prod) = 59850521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_587
      · exact prime_eightyThreeCC_2549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59850521) ^ 29925260 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 59850521) ^ 11970104 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 59850521) ^ 101960 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 59850521) ^ 23480 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_71681921 : Nat.Prime 71681921 := by
  apply lucas_primality 71681921 (6 : ZMod 71681921)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (31, 1), (3613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (31, 1), (3613, 1)] : List FactorBlock).map factorBlockValue).prod) = 71681921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_31
      · exact prime_eightyThreeCC_3613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 71681921) ^ 35840960 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 71681921) ^ 14336384 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 71681921) ^ 2312320 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 71681921) ^ 19840 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_75602603 : Nat.Prime 75602603 := by
  apply lucas_primality 75602603 (2 : ZMod 75602603)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (804283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (804283, 1)] : List FactorBlock).map factorBlockValue).prod) = 75602603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_47
      · exact prime_eightyThreeCC_804283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75602603) ^ 37801301 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 75602603) ^ 1608566 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 75602603) ^ 94 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_78491173 : Nat.Prime 78491173 := by
  apply lucas_primality 78491173 (2 : ZMod 78491173)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (199, 1), (32869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (199, 1), (32869, 1)] : List FactorBlock).map factorBlockValue).prod) = 78491173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_199
      · exact prime_eightyThreeCC_32869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 78491173) ^ 39245586 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 78491173) ^ 26163724 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 78491173) ^ 394428 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 78491173) ^ 2388 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_81504923 : Nat.Prime 81504923 := by
  apply lucas_primality 81504923 (2 : ZMod 81504923)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (40752461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (40752461, 1)] : List FactorBlock).map factorBlockValue).prod) = 81504923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_40752461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 81504923) ^ 40752461 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 81504923) ^ 2 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_86969549 : Nat.Prime 86969549 := by
  apply lucas_primality 86969549 (2 : ZMod 86969549)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (659, 1), (32993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (659, 1), (32993, 1)] : List FactorBlock).map factorBlockValue).prod) = 86969549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_659
      · exact prime_eightyThreeCC_32993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86969549) ^ 43484774 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 86969549) ^ 131972 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 86969549) ^ 2636 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_92323499 : Nat.Prime 92323499 := by
  apply lucas_primality 92323499 (2 : ZMod 92323499)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1549, 1), (1753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1549, 1), (1753, 1)] : List FactorBlock).map factorBlockValue).prod) = 92323499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_1549
      · exact prime_eightyThreeCC_1753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 92323499) ^ 46161749 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92323499) ^ 5430794 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92323499) ^ 59602 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92323499) ^ 52666 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_95690083 : Nat.Prime 95690083 := by
  apply lucas_primality 95690083 (5 : ZMod 95690083)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (549943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (549943, 1)] : List FactorBlock).map factorBlockValue).prod) = 95690083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_29
      · exact prime_eightyThreeCC_549943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 95690083) ^ 47845041 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 95690083) ^ 31896694 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 95690083) ^ 3299658 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 95690083) ^ 174 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_95756821 : Nat.Prime 95756821 := by
  apply lucas_primality 95756821 (7 : ZMod 95756821)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (69389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (69389, 1)] : List FactorBlock).map factorBlockValue).prod) = 95756821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_69389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 95756821) ^ 47878410 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 95756821) ^ 31918940 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 95756821) ^ 19151364 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 95756821) ^ 4163340 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 95756821) ^ 1380 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_99008671 : Nat.Prime 99008671 := by
  apply lucas_primality 99008671 (11 : ZMod 99008671)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (191, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (191, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 99008671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_37
      · exact prime_eightyThreeCC_191
      · exact prime_eightyThreeCC_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 99008671) ^ 49504335 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 99008671) ^ 33002890 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 99008671) ^ 19801734 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 99008671) ^ 2675910 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 99008671) ^ 518370 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 99008671) ^ 212010 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_106521937 : Nat.Prime 106521937 := by
  apply lucas_primality 106521937 (5 : ZMod 106521937)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (113, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (113, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 106521937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_41
      · exact prime_eightyThreeCC_113
      · exact prime_eightyThreeCC_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 106521937) ^ 53260968 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 106521937) ^ 35507312 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 106521937) ^ 2598096 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 106521937) ^ 942672 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 106521937) ^ 222384 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_109504883 : Nat.Prime 109504883 := by
  apply lucas_primality 109504883 (2 : ZMod 109504883)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (897581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (897581, 1)] : List FactorBlock).map factorBlockValue).prod) = 109504883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_61
      · exact prime_eightyThreeCC_897581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 109504883) ^ 54752441 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 109504883) ^ 1795162 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 109504883) ^ 122 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_122297377 : Nat.Prime 122297377 := by
  apply lucas_primality 122297377 (7 : ZMod 122297377)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (19, 1), (67049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (19, 1), (67049, 1)] : List FactorBlock).map factorBlockValue).prod) = 122297377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_67049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 122297377) ^ 61148688 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 122297377) ^ 40765792 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 122297377) ^ 6436704 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 122297377) ^ 1824 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_128962439 : Nat.Prime 128962439 := by
  apply lucas_primality 128962439 (7 : ZMod 128962439)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (5861929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (5861929, 1)] : List FactorBlock).map factorBlockValue).prod) = 128962439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_5861929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 128962439) ^ 64481219 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 128962439) ^ 11723858 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 128962439) ^ 22 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_133306423 : Nat.Prime 133306423 := by
  apply lucas_primality 133306423 (3 : ZMod 133306423)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (22217737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (22217737, 1)] : List FactorBlock).map factorBlockValue).prod) = 133306423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_22217737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 133306423) ^ 66653211 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 133306423) ^ 44435474 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 133306423) ^ 6 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_136737877 : Nat.Prime 136737877 := by
  apply lucas_primality 136737877 (2 : ZMod 136737877)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (1035893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (1035893, 1)] : List FactorBlock).map factorBlockValue).prod) = 136737877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_1035893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 136737877) ^ 68368938 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 136737877) ^ 45579292 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 136737877) ^ 12430716 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 136737877) ^ 132 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_139314823 : Nat.Prime 139314823 := by
  apply lucas_primality 139314823 (5 : ZMod 139314823)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (449, 1), (51713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (449, 1), (51713, 1)] : List FactorBlock).map factorBlockValue).prod) = 139314823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_449
      · exact prime_eightyThreeCC_51713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 139314823) ^ 69657411 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 139314823) ^ 46438274 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 139314823) ^ 310278 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 139314823) ^ 2694 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_140129443 : Nat.Prime 140129443 := by
  apply lucas_primality 140129443 (2 : ZMod 140129443)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (191, 1), (40759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (191, 1), (40759, 1)] : List FactorBlock).map factorBlockValue).prod) = 140129443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_191
      · exact prime_eightyThreeCC_40759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 140129443) ^ 70064721 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 140129443) ^ 46709814 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 140129443) ^ 733662 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 140129443) ^ 3438 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_140970721 : Nat.Prime 140970721 := by
  apply lucas_primality 140970721 (13 : ZMod 140970721)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (11, 1), (26699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (11, 1), (26699, 1)] : List FactorBlock).map factorBlockValue).prod) = 140970721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_26699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 140970721) ^ 70485360 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 140970721) ^ 46990240 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 140970721) ^ 28194144 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 140970721) ^ 12815520 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 140970721) ^ 5280 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_146516317 : Nat.Prime 146516317 := by
  apply lucas_primality 146516317 (2 : ZMod 146516317)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (571, 1), (21383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (571, 1), (21383, 1)] : List FactorBlock).map factorBlockValue).prod) = 146516317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_571
      · exact prime_eightyThreeCC_21383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 146516317) ^ 73258158 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 146516317) ^ 48838772 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 146516317) ^ 256596 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 146516317) ^ 6852 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_153741239 : Nat.Prime 153741239 := by
  apply lucas_primality 153741239 (7 : ZMod 153741239)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (107, 1), (3539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (107, 1), (3539, 1)] : List FactorBlock).map factorBlockValue).prod) = 153741239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_29
      · exact prime_eightyThreeCC_107
      · exact prime_eightyThreeCC_3539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 153741239) ^ 76870619 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 153741239) ^ 21963034 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 153741239) ^ 5301422 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 153741239) ^ 1436834 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 153741239) ^ 43442 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_203417407 : Nat.Prime 203417407 := by
  apply lucas_primality 203417407 (5 : ZMod 203417407)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (1255663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (1255663, 1)] : List FactorBlock).map factorBlockValue).prod) = 203417407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_1255663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 203417407) ^ 101708703 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 203417407) ^ 67805802 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 203417407) ^ 162 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_219009767 : Nat.Prime 219009767 := by
  apply lucas_primality 219009767 (5 : ZMod 219009767)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109504883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109504883, 1)] : List FactorBlock).map factorBlockValue).prod) = 219009767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_109504883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 219009767) ^ 109504883 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 219009767) ^ 2 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_223067167 : Nat.Prime 223067167 := by
  apply lucas_primality 223067167 (3 : ZMod 223067167)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (151, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (151, 1), (2069, 1)] : List FactorBlock).map factorBlockValue).prod) = 223067167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_151
      · exact prime_eightyThreeCC_2069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 223067167) ^ 111533583 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 223067167) ^ 74355722 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 223067167) ^ 31866738 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 223067167) ^ 13121598 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 223067167) ^ 1477266 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 223067167) ^ 107814 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_252718901 : Nat.Prime 252718901 := by
  apply lucas_primality 252718901 (2 : ZMod 252718901)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (149, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (149, 1), (2423, 1)] : List FactorBlock).map factorBlockValue).prod) = 252718901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_149
      · exact prime_eightyThreeCC_2423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 252718901) ^ 126359450 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 252718901) ^ 50543780 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 252718901) ^ 36102700 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 252718901) ^ 1696100 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 252718901) ^ 104300 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_315355567 : Nat.Prime 315355567 := by
  apply lucas_primality 315355567 (3 : ZMod 315355567)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (52559261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (52559261, 1)] : List FactorBlock).map factorBlockValue).prod) = 315355567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_52559261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 315355567) ^ 157677783 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 315355567) ^ 105118522 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 315355567) ^ 6 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_331059473 : Nat.Prime 331059473 := by
  apply lucas_primality 331059473 (3 : ZMod 331059473)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (20691217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (20691217, 1)] : List FactorBlock).map factorBlockValue).prod) = 331059473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_20691217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 331059473) ^ 165529736 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 331059473) ^ 16 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_350174557 : Nat.Prime 350174557 := by
  apply lucas_primality 350174557 (2 : ZMod 350174557)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (71, 1), (45667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (71, 1), (45667, 1)] : List FactorBlock).map factorBlockValue).prod) = 350174557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_71
      · exact prime_eightyThreeCC_45667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 350174557) ^ 175087278 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 350174557) ^ 116724852 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 350174557) ^ 4932036 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 350174557) ^ 7668 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_352347769 : Nat.Prime 352347769 := by
  apply lucas_primality 352347769 (17 : ZMod 352347769)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (41, 1), (119359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (41, 1), (119359, 1)] : List FactorBlock).map factorBlockValue).prod) = 352347769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_41
      · exact prime_eightyThreeCC_119359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 352347769) ^ 176173884 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 352347769) ^ 117449256 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 352347769) ^ 8593848 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 352347769) ^ 2952 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_387939637 : Nat.Prime 387939637 := by
  apply lucas_primality 387939637 (5 : ZMod 387939637)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (43, 1), (35801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (43, 1), (35801, 1)] : List FactorBlock).map factorBlockValue).prod) = 387939637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_43
      · exact prime_eightyThreeCC_35801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 387939637) ^ 193969818 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 387939637) ^ 129313212 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 387939637) ^ 55419948 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 387939637) ^ 9021852 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 387939637) ^ 10836 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_401234143 : Nat.Prime 401234143 := by
  apply lucas_primality 401234143 (5 : ZMod 401234143)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (1807361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (1807361, 1)] : List FactorBlock).map factorBlockValue).prod) = 401234143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_37
      · exact prime_eightyThreeCC_1807361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 401234143) ^ 200617071 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 401234143) ^ 133744714 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 401234143) ^ 10844166 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 401234143) ^ 222 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_425538493 : Nat.Prime 425538493 := by
  apply lucas_primality 425538493 (2 : ZMod 425538493)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (43, 1), (139, 1), (349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (43, 1), (139, 1), (349, 1)] : List FactorBlock).map factorBlockValue).prod) = 425538493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_43
      · exact prime_eightyThreeCC_139
      · exact prime_eightyThreeCC_349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 425538493) ^ 212769246 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 425538493) ^ 141846164 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 425538493) ^ 25031676 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 425538493) ^ 9896244 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 425538493) ^ 3061428 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 425538493) ^ 1219308 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_477312697 : Nat.Prime 477312697 := by
  apply lucas_primality 477312697 (5 : ZMod 477312697)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (89, 1), (3547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (89, 1), (3547, 1)] : List FactorBlock).map factorBlockValue).prod) = 477312697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_89
      · exact prime_eightyThreeCC_3547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 477312697) ^ 238656348 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 477312697) ^ 159104232 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 477312697) ^ 68187528 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 477312697) ^ 5363064 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 477312697) ^ 134568 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_503131591 : Nat.Prime 503131591 := by
  apply lucas_primality 503131591 (3 : ZMod 503131591)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 2), (19, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 2), (19, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) = 503131591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_1741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 503131591) ^ 251565795 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 503131591) ^ 167710530 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 503131591) ^ 100626318 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 503131591) ^ 38702430 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 503131591) ^ 26480610 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 503131591) ^ 288990 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_549781933 : Nat.Prime 549781933 := by
  apply lucas_primality 549781933 (2 : ZMod 549781933)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (53, 1), (123491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (53, 1), (123491, 1)] : List FactorBlock).map factorBlockValue).prod) = 549781933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_53
      · exact prime_eightyThreeCC_123491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 549781933) ^ 274890966 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 549781933) ^ 183260644 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 549781933) ^ 78540276 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 549781933) ^ 10373244 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 549781933) ^ 4452 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_554625373 : Nat.Prime 554625373 := by
  apply lucas_primality 554625373 (5 : ZMod 554625373)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (6602683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (6602683, 1)] : List FactorBlock).map factorBlockValue).prod) = 554625373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_6602683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 554625373) ^ 277312686 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 554625373) ^ 184875124 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 554625373) ^ 79232196 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 554625373) ^ 84 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_574540927 : Nat.Prime 574540927 := by
  apply lucas_primality 574540927 (3 : ZMod 574540927)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (95756821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (95756821, 1)] : List FactorBlock).map factorBlockValue).prod) = 574540927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_95756821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 574540927) ^ 287270463 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 574540927) ^ 191513642 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 574540927) ^ 6 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_592793701 : Nat.Prime 592793701 := by
  apply lucas_primality 592793701 (10 : ZMod 592793701)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (43, 1), (45953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (43, 1), (45953, 1)] : List FactorBlock).map factorBlockValue).prod) = 592793701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_43
      · exact prime_eightyThreeCC_45953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 592793701) ^ 296396850 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 592793701) ^ 197597900 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 592793701) ^ 118558740 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 592793701) ^ 13785900 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 592793701) ^ 12900 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_595309171 : Nat.Prime 595309171 := by
  apply lucas_primality 595309171 (3 : ZMod 595309171)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4241, 1), (4679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4241, 1), (4679, 1)] : List FactorBlock).map factorBlockValue).prod) = 595309171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_4241
      · exact prime_eightyThreeCC_4679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 595309171) ^ 297654585 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 595309171) ^ 198436390 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 595309171) ^ 119061834 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 595309171) ^ 140370 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 595309171) ^ 127230 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_622538467 : Nat.Prime 622538467 := by
  apply lucas_primality 622538467 (2 : ZMod 622538467)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (31, 1), (139, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (31, 1), (139, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) = 622538467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_31
      · exact prime_eightyThreeCC_139
      · exact prime_eightyThreeCC_199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 622538467) ^ 311269233 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 622538467) ^ 207512822 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 622538467) ^ 56594406 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 622538467) ^ 20081886 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 622538467) ^ 4478694 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 622538467) ^ 3128334 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_626743283 : Nat.Prime 626743283 := by
  apply lucas_primality 626743283 (2 : ZMod 626743283)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (607, 1), (46933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (607, 1), (46933, 1)] : List FactorBlock).map factorBlockValue).prod) = 626743283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_607
      · exact prime_eightyThreeCC_46933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 626743283) ^ 313371641 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 626743283) ^ 56976662 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 626743283) ^ 1032526 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 626743283) ^ 13354 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_697782359 : Nat.Prime 697782359 := by
  apply lucas_primality 697782359 (7 : ZMod 697782359)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (103, 1), (37223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (103, 1), (37223, 1)] : List FactorBlock).map factorBlockValue).prod) = 697782359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_103
      · exact prime_eightyThreeCC_37223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 697782359) ^ 348891179 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 697782359) ^ 99683194 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 697782359) ^ 53675566 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 697782359) ^ 6774586 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 697782359) ^ 18746 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_706741331 : Nat.Prime 706741331 := by
  apply lucas_primality 706741331 (2 : ZMod 706741331)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (139, 1), (173, 1), (2939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (139, 1), (173, 1), (2939, 1)] : List FactorBlock).map factorBlockValue).prod) = 706741331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_139
      · exact prime_eightyThreeCC_173
      · exact prime_eightyThreeCC_2939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 706741331) ^ 353370665 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 706741331) ^ 141348266 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 706741331) ^ 5084470 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 706741331) ^ 4085210 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 706741331) ^ 240470 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_730174639 : Nat.Prime 730174639 := by
  apply lucas_primality 730174639 (6 : ZMod 730174639)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (641, 1), (189853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (641, 1), (189853, 1)] : List FactorBlock).map factorBlockValue).prod) = 730174639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_641
      · exact prime_eightyThreeCC_189853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 730174639) ^ 365087319 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 730174639) ^ 243391546 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 730174639) ^ 1139118 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 730174639) ^ 3846 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_738385111 : Nat.Prime 738385111 := by
  apply lucas_primality 738385111 (3 : ZMod 738385111)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (163, 1), (50333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (163, 1), (50333, 1)] : List FactorBlock).map factorBlockValue).prod) = 738385111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_163
      · exact prime_eightyThreeCC_50333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 738385111) ^ 369192555 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 738385111) ^ 246128370 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 738385111) ^ 147677022 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 738385111) ^ 4529970 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 738385111) ^ 14670 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_865187809 : Nat.Prime 865187809 := by
  apply lucas_primality 865187809 (7 : ZMod 865187809)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (383, 1), (23531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (383, 1), (23531, 1)] : List FactorBlock).map factorBlockValue).prod) = 865187809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_383
      · exact prime_eightyThreeCC_23531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 865187809) ^ 432593904 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 865187809) ^ 288395936 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 865187809) ^ 2258976 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 865187809) ^ 36768 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_892707943 : Nat.Prime 892707943 := by
  apply lucas_primality 892707943 (3 : ZMod 892707943)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (47, 1), (452233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (47, 1), (452233, 1)] : List FactorBlock).map factorBlockValue).prod) = 892707943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_47
      · exact prime_eightyThreeCC_452233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 892707943) ^ 446353971 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 892707943) ^ 297569314 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 892707943) ^ 127529706 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 892707943) ^ 18993786 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 892707943) ^ 1974 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1173268081 : Nat.Prime 1173268081 := by
  apply lucas_primality 1173268081 (14 : ZMod 1173268081)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (29, 1), (83, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (29, 1), (83, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 1173268081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_29
      · exact prime_eightyThreeCC_83
      · exact prime_eightyThreeCC_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1173268081) ^ 586634040 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (14 : ZMod 1173268081) ^ 391089360 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (14 : ZMod 1173268081) ^ 234653616 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (14 : ZMod 1173268081) ^ 40457520 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (14 : ZMod 1173268081) ^ 14135760 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (14 : ZMod 1173268081) ^ 1733040 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1368368173 : Nat.Prime 1368368173 := by
  apply lucas_primality 1368368173 (2 : ZMod 1368368173)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (38010227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (38010227, 1)] : List FactorBlock).map factorBlockValue).prod) = 1368368173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_38010227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1368368173) ^ 684184086 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1368368173) ^ 456122724 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1368368173) ^ 36 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_2158034941 : Nat.Prime 2158034941 := by
  apply lucas_primality 2158034941 (2 : ZMod 2158034941)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (3996361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (3996361, 1)] : List FactorBlock).map factorBlockValue).prod) = 2158034941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_3996361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2158034941) ^ 1079017470 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2158034941) ^ 719344980 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2158034941) ^ 431606988 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2158034941) ^ 540 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_2161963961 : Nat.Prime 2161963961 := by
  apply lucas_primality 2161963961 (3 : ZMod 2161963961)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (4157623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (4157623, 1)] : List FactorBlock).map factorBlockValue).prod) = 2161963961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_4157623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2161963961) ^ 1080981980 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2161963961) ^ 432392792 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2161963961) ^ 166304920 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2161963961) ^ 520 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_2186812063 : Nat.Prime 2186812063 := by
  apply lucas_primality 2186812063 (5 : ZMod 2186812063)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (1813277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (1813277, 1)] : List FactorBlock).map factorBlockValue).prod) = 2186812063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_67
      · exact prime_eightyThreeCC_1813277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2186812063) ^ 1093406031 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2186812063) ^ 728937354 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2186812063) ^ 32638986 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2186812063) ^ 1206 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_3287973433 : Nat.Prime 3287973433 := by
  apply lucas_primality 3287973433 (5 : ZMod 3287973433)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1637, 1), (83689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1637, 1), (83689, 1)] : List FactorBlock).map factorBlockValue).prod) = 3287973433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_1637
      · exact prime_eightyThreeCC_83689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3287973433) ^ 1643986716 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3287973433) ^ 1095991144 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3287973433) ^ 2008536 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3287973433) ^ 39288 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_3442261481 : Nat.Prime 3442261481 := by
  apply lucas_primality 3442261481 (3 : ZMod 3442261481)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (12293791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (12293791, 1)] : List FactorBlock).map factorBlockValue).prod) = 3442261481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_12293791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3442261481) ^ 1721130740 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3442261481) ^ 688452296 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3442261481) ^ 491751640 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3442261481) ^ 280 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_3556235509 : Nat.Prime 3556235509 := by
  apply lucas_primality 3556235509 (6 : ZMod 3556235509)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (659, 1), (3779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (659, 1), (3779, 1)] : List FactorBlock).map factorBlockValue).prod) = 3556235509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_659
      · exact prime_eightyThreeCC_3779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3556235509) ^ 1778117754 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 3556235509) ^ 1185411836 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 3556235509) ^ 508033644 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 3556235509) ^ 209190324 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 3556235509) ^ 5396412 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 3556235509) ^ 941052 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_3570831773 : Nat.Prime 3570831773 := by
  apply lucas_primality 3570831773 (2 : ZMod 3570831773)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (892707943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (892707943, 1)] : List FactorBlock).map factorBlockValue).prod) = 3570831773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_892707943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3570831773) ^ 1785415886 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3570831773) ^ 4 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_3644277379 : Nat.Prime 3644277379 := by
  apply lucas_primality 3644277379 (2 : ZMod 3644277379)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (271, 1), (320179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (271, 1), (320179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3644277379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_271
      · exact prime_eightyThreeCC_320179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3644277379) ^ 1822138689 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3644277379) ^ 1214759126 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3644277379) ^ 520611054 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3644277379) ^ 13447518 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3644277379) ^ 11382 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_4249423033 : Nat.Prime 4249423033 := by
  apply lucas_primality 4249423033 (5 : ZMod 4249423033)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (3767219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (3767219, 1)] : List FactorBlock).map factorBlockValue).prod) = 4249423033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_47
      · exact prime_eightyThreeCC_3767219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4249423033) ^ 2124711516 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4249423033) ^ 1416474344 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4249423033) ^ 90413256 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4249423033) ^ 1128 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_4606435133 : Nat.Prime 4606435133 := by
  apply lucas_primality 4606435133 (3 : ZMod 4606435133)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1913, 1), (46307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1913, 1), (46307, 1)] : List FactorBlock).map factorBlockValue).prod) = 4606435133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_1913
      · exact prime_eightyThreeCC_46307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4606435133) ^ 2303217566 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4606435133) ^ 354341164 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4606435133) ^ 2407964 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4606435133) ^ 99476 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_4797329951 : Nat.Prime 4797329951 := by
  apply lucas_primality 4797329951 (7 : ZMod 4797329951)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (19, 1), (47, 1), (15349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (19, 1), (47, 1), (15349, 1)] : List FactorBlock).map factorBlockValue).prod) = 4797329951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_47
      · exact prime_eightyThreeCC_15349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4797329951) ^ 2398664975 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4797329951) ^ 959465990 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4797329951) ^ 685332850 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4797329951) ^ 252491050 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4797329951) ^ 102070850 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4797329951) ^ 312550 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5069636879 : Nat.Prime 5069636879 := by
  apply lucas_primality 5069636879 (13 : ZMod 5069636879)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (53, 1), (2813339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (53, 1), (2813339, 1)] : List FactorBlock).map factorBlockValue).prod) = 5069636879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_53
      · exact prime_eightyThreeCC_2813339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 5069636879) ^ 2534818439 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 5069636879) ^ 298213934 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 5069636879) ^ 95653526 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 5069636879) ^ 1802 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5218172941 : Nat.Prime 5218172941 := by
  apply lucas_primality 5218172941 (2 : ZMod 5218172941)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (86969549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (86969549, 1)] : List FactorBlock).map factorBlockValue).prod) = 5218172941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_86969549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5218172941) ^ 2609086470 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5218172941) ^ 1739390980 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5218172941) ^ 1043634588 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5218172941) ^ 60 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5836793117 : Nat.Prime 5836793117 := by
  apply lucas_primality 5836793117 (2 : ZMod 5836793117)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (53, 1), (357559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (53, 1), (357559, 1)] : List FactorBlock).map factorBlockValue).prod) = 5836793117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_53
      · exact prime_eightyThreeCC_357559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5836793117) ^ 2918396558 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5836793117) ^ 833827588 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5836793117) ^ 530617556 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5836793117) ^ 110128172 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5836793117) ^ 16324 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5956676311 : Nat.Prime 5956676311 := by
  apply lucas_primality 5956676311 (3 : ZMod 5956676311)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (15273529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (15273529, 1)] : List FactorBlock).map factorBlockValue).prod) = 5956676311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_15273529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5956676311) ^ 2978338155 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5956676311) ^ 1985558770 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5956676311) ^ 1191335262 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5956676311) ^ 458205870 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5956676311) ^ 390 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5975280979 : Nat.Prime 5975280979 := by
  apply lucas_primality 5975280979 (2 : ZMod 5975280979)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2531, 1), (393473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2531, 1), (393473, 1)] : List FactorBlock).map factorBlockValue).prod) = 5975280979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_2531
      · exact prime_eightyThreeCC_393473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5975280979) ^ 2987640489 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975280979) ^ 1991760326 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975280979) ^ 2360838 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975280979) ^ 15186 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_6181116559 : Nat.Prime 6181116559 := by
  apply lucas_primality 6181116559 (3 : ZMod 6181116559)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (6168779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (6168779, 1)] : List FactorBlock).map factorBlockValue).prod) = 6181116559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_167
      · exact prime_eightyThreeCC_6168779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6181116559) ^ 3090558279 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6181116559) ^ 2060372186 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6181116559) ^ 37012674 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6181116559) ^ 1002 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_6625001203 : Nat.Prime 6625001203 := by
  apply lucas_primality 6625001203 (2 : ZMod 6625001203)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2719, 1), (406093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2719, 1), (406093, 1)] : List FactorBlock).map factorBlockValue).prod) = 6625001203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_2719
      · exact prime_eightyThreeCC_406093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6625001203) ^ 3312500601 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625001203) ^ 2208333734 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625001203) ^ 2436558 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6625001203) ^ 16314 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_8204272621 : Nat.Prime 8204272621 := by
  apply lucas_primality 8204272621 (2 : ZMod 8204272621)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (136737877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (136737877, 1)] : List FactorBlock).map factorBlockValue).prod) = 8204272621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_136737877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8204272621) ^ 4102136310 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8204272621) ^ 2734757540 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8204272621) ^ 1640854524 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8204272621) ^ 60 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_9254916857 : Nat.Prime 9254916857 := by
  apply lucas_primality 9254916857 (3 : ZMod 9254916857)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (37, 1), (1078159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (37, 1), (1078159, 1)] : List FactorBlock).map factorBlockValue).prod) = 9254916857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_29
      · exact prime_eightyThreeCC_37
      · exact prime_eightyThreeCC_1078159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9254916857) ^ 4627458428 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9254916857) ^ 319135064 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9254916857) ^ 250132888 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9254916857) ^ 8584 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_10073437357 : Nat.Prime 10073437357 := by
  apply lucas_primality 10073437357 (6 : ZMod 10073437357)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2309, 1), (363557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2309, 1), (363557, 1)] : List FactorBlock).map factorBlockValue).prod) = 10073437357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_2309
      · exact prime_eightyThreeCC_363557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 10073437357) ^ 5036718678 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 10073437357) ^ 3357812452 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 10073437357) ^ 4362684 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 10073437357) ^ 27708 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_10503879143 : Nat.Prime 10503879143 := by
  apply lucas_primality 10503879143 (5 : ZMod 10503879143)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (499, 1), (10524929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (499, 1), (10524929, 1)] : List FactorBlock).map factorBlockValue).prod) = 10503879143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_499
      · exact prime_eightyThreeCC_10524929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10503879143) ^ 5251939571 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 10503879143) ^ 21049858 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 10503879143) ^ 998 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_10650752509 : Nat.Prime 10650752509 := by
  apply lucas_primality 10650752509 (7 : ZMod 10650752509)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 3), (23, 1), (79, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 3), (23, 1), (79, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod) = 10650752509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_79
      · exact prime_eightyThreeCC_367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10650752509) ^ 5325376254 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 10650752509) ^ 3550250836 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 10650752509) ^ 968250228 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 10650752509) ^ 463076196 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 10650752509) ^ 134819652 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 10650752509) ^ 29021124 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_11341739411 : Nat.Prime 11341739411 := by
  apply lucas_primality 11341739411 (2 : ZMod 11341739411)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7541, 1), (150401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7541, 1), (150401, 1)] : List FactorBlock).map factorBlockValue).prod) = 11341739411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7541
      · exact prime_eightyThreeCC_150401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11341739411) ^ 5670869705 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11341739411) ^ 2268347882 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11341739411) ^ 1504010 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11341739411) ^ 75410 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_11896469033 : Nat.Prime 11896469033 := by
  apply lucas_primality 11896469033 (3 : ZMod 11896469033)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (17, 1), (23, 1), (311, 1), (1747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (17, 1), (23, 1), (311, 1), (1747, 1)] : List FactorBlock).map factorBlockValue).prod) = 11896469033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_311
      · exact prime_eightyThreeCC_1747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11896469033) ^ 5948234516 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11896469033) ^ 1699495576 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11896469033) ^ 699792296 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11896469033) ^ 517237784 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11896469033) ^ 38252312 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11896469033) ^ 6809656 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_12971783767 : Nat.Prime 12971783767 := by
  apply lucas_primality 12971783767 (5 : ZMod 12971783767)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2161963961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2161963961, 1)] : List FactorBlock).map factorBlockValue).prod) = 12971783767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_2161963961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12971783767) ^ 6485891883 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12971783767) ^ 4323927922 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 12971783767) ^ 6 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_13918949441 : Nat.Prime 13918949441 := by
  apply lucas_primality 13918949441 (3 : ZMod 13918949441)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (11, 2), (359477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (11, 2), (359477, 1)] : List FactorBlock).map factorBlockValue).prod) = 13918949441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_359477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13918949441) ^ 6959474720 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13918949441) ^ 2783789888 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13918949441) ^ 1265359040 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 13918949441) ^ 38720 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_14106252119 : Nat.Prime 14106252119 := by
  apply lucas_primality 14106252119 (7 : ZMod 14106252119)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (53031023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (53031023, 1)] : List FactorBlock).map factorBlockValue).prod) = 14106252119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_53031023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 14106252119) ^ 7053126059 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14106252119) ^ 2015178874 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14106252119) ^ 742434322 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 14106252119) ^ 266 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_14746287463 : Nat.Prime 14746287463 := by
  apply lucas_primality 14746287463 (3 : ZMod 14746287463)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (29611019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (29611019, 1)] : List FactorBlock).map factorBlockValue).prod) = 14746287463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_83
      · exact prime_eightyThreeCC_29611019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14746287463) ^ 7373143731 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 14746287463) ^ 4915429154 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 14746287463) ^ 177666114 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 14746287463) ^ 498 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_16636918421 : Nat.Prime 16636918421 := by
  apply lucas_primality 16636918421 (2 : ZMod 16636918421)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (1583, 1), (30911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (1583, 1), (30911, 1)] : List FactorBlock).map factorBlockValue).prod) = 16636918421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_1583
      · exact prime_eightyThreeCC_30911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16636918421) ^ 8318459210 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 16636918421) ^ 3327383684 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 16636918421) ^ 978642260 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 16636918421) ^ 10509740 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 16636918421) ^ 538220 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_18618224143 : Nat.Prime 18618224143 := by
  apply lucas_primality 18618224143 (3 : ZMod 18618224143)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (163, 1), (443, 1), (877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (163, 1), (443, 1), (877, 1)] : List FactorBlock).map factorBlockValue).prod) = 18618224143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_163
      · exact prime_eightyThreeCC_443
      · exact prime_eightyThreeCC_877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18618224143) ^ 9309112071 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 18618224143) ^ 6206074714 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 18618224143) ^ 2659746306 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 18618224143) ^ 114222234 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 18618224143) ^ 42027594 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 18618224143) ^ 21229446 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_20379490357 : Nat.Prime 20379490357 := by
  apply lucas_primality 20379490357 (2 : ZMod 20379490357)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (127, 1), (919, 1), (14551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (127, 1), (919, 1), (14551, 1)] : List FactorBlock).map factorBlockValue).prod) = 20379490357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_127
      · exact prime_eightyThreeCC_919
      · exact prime_eightyThreeCC_14551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20379490357) ^ 10189745178 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20379490357) ^ 6793163452 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20379490357) ^ 160468428 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20379490357) ^ 22175724 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20379490357) ^ 1400556 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_21118825459 : Nat.Prime 21118825459 := by
  apply lucas_primality 21118825459 (2 : ZMod 21118825459)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1173268081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1173268081, 1)] : List FactorBlock).map factorBlockValue).prod) = 21118825459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_1173268081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21118825459) ^ 10559412729 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21118825459) ^ 7039608486 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21118825459) ^ 18 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_21804494731 : Nat.Prime 21804494731 := by
  apply lucas_primality 21804494731 (10 : ZMod 21804494731)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (31600717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (31600717, 1)] : List FactorBlock).map factorBlockValue).prod) = 21804494731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_31600717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 21804494731) ^ 10902247365 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 21804494731) ^ 7268164910 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 21804494731) ^ 4360898946 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 21804494731) ^ 948021510 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 21804494731) ^ 690 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_23873154013 : Nat.Prime 23873154013 := by
  apply lucas_primality 23873154013 (2 : ZMod 23873154013)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1361, 1), (487247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1361, 1), (487247, 1)] : List FactorBlock).map factorBlockValue).prod) = 23873154013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_1361
      · exact prime_eightyThreeCC_487247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23873154013) ^ 11936577006 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 23873154013) ^ 7957718004 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 23873154013) ^ 17540892 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 23873154013) ^ 48996 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_24392410703 : Nat.Prime 24392410703 := by
  apply lucas_primality 24392410703 (5 : ZMod 24392410703)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (127, 1), (8730283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (127, 1), (8730283, 1)] : List FactorBlock).map factorBlockValue).prod) = 24392410703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_127
      · exact prime_eightyThreeCC_8730283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24392410703) ^ 12196205351 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24392410703) ^ 2217491882 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24392410703) ^ 192066226 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24392410703) ^ 2794 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_25386843203 : Nat.Prime 25386843203 := by
  apply lucas_primality 25386843203 (2 : ZMod 25386843203)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (149, 1), (206273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (149, 1), (206273, 1)] : List FactorBlock).map factorBlockValue).prod) = 25386843203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_59
      · exact prime_eightyThreeCC_149
      · exact prime_eightyThreeCC_206273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25386843203) ^ 12693421601 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 25386843203) ^ 3626691886 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 25386843203) ^ 430285478 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 25386843203) ^ 170381498 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 25386843203) ^ 123074 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_27837898883 : Nat.Prime 27837898883 := by
  apply lucas_primality 27837898883 (2 : ZMod 27837898883)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13918949441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13918949441, 1)] : List FactorBlock).map factorBlockValue).prod) = 27837898883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_13918949441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 27837898883) ^ 13918949441 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 27837898883) ^ 2 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_28212504239 : Nat.Prime 28212504239 := by
  apply lucas_primality 28212504239 (23 : ZMod 28212504239)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14106252119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14106252119, 1)] : List FactorBlock).map factorBlockValue).prod) = 28212504239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_14106252119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (23 : ZMod 28212504239) ^ 14106252119 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (23 : ZMod 28212504239) ^ 2 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_28503193681 : Nat.Prime 28503193681 := by
  apply lucas_primality 28503193681 (11 : ZMod 28503193681)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (5, 1), (13, 1), (79, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (5, 1), (13, 1), (79, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod) = 28503193681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_79
      · exact prime_eightyThreeCC_4283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 28503193681) ^ 14251596840 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 28503193681) ^ 9501064560 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 28503193681) ^ 5700638736 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 28503193681) ^ 2192553360 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 28503193681) ^ 360799920 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 28503193681) ^ 6654960 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_39991926901 : Nat.Prime 39991926901 := by
  apply lucas_primality 39991926901 (6 : ZMod 39991926901)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (133306423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (133306423, 1)] : List FactorBlock).map factorBlockValue).prod) = 39991926901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_133306423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 39991926901) ^ 19995963450 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 39991926901) ^ 13330642300 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 39991926901) ^ 7998385380 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 39991926901) ^ 300 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_56042731733 : Nat.Prime 56042731733 := by
  apply lucas_primality 56042731733 (2 : ZMod 56042731733)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (101, 1), (953, 1), (11197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (101, 1), (953, 1), (11197, 1)] : List FactorBlock).map factorBlockValue).prod) = 56042731733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_101
      · exact prime_eightyThreeCC_953
      · exact prime_eightyThreeCC_11197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56042731733) ^ 28021365866 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 56042731733) ^ 4310979364 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 56042731733) ^ 554878532 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 56042731733) ^ 58806644 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 56042731733) ^ 5005156 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_59848289381 : Nat.Prime 59848289381 := by
  apply lucas_primality 59848289381 (2 : ZMod 59848289381)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (31, 1), (8775409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (31, 1), (8775409, 1)] : List FactorBlock).map factorBlockValue).prod) = 59848289381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_31
      · exact prime_eightyThreeCC_8775409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59848289381) ^ 29924144690 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 59848289381) ^ 11969657876 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 59848289381) ^ 5440753580 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 59848289381) ^ 1930589980 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 59848289381) ^ 6820 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_60603816269 : Nat.Prime 60603816269 := by
  apply lucas_primality 60603816269 (2 : ZMod 60603816269)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (352347769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (352347769, 1)] : List FactorBlock).map factorBlockValue).prod) = 60603816269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_43
      · exact prime_eightyThreeCC_352347769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60603816269) ^ 30301908134 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 60603816269) ^ 1409391076 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 60603816269) ^ 172 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_62618075293 : Nat.Prime 62618075293 := by
  apply lucas_primality 62618075293 (2 : ZMod 62618075293)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5218172941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5218172941, 1)] : List FactorBlock).map factorBlockValue).prod) = 62618075293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5218172941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 62618075293) ^ 31309037646 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 62618075293) ^ 20872691764 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 62618075293) ^ 12 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_74191205017 : Nat.Prime 74191205017 := by
  apply lucas_primality 74191205017 (5 : ZMod 74191205017)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (19, 1), (18077779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (19, 1), (18077779, 1)] : List FactorBlock).map factorBlockValue).prod) = 74191205017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_18077779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 74191205017) ^ 37095602508 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 74191205017) ^ 24730401672 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 74191205017) ^ 3904800264 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 74191205017) ^ 4104 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_86528513413 : Nat.Prime 86528513413 := by
  apply lucas_primality 86528513413 (2 : ZMod 86528513413)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (11, 1), (2131, 1), (11393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (11, 1), (2131, 1), (11393, 1)] : List FactorBlock).map factorBlockValue).prod) = 86528513413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_2131
      · exact prime_eightyThreeCC_11393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 86528513413) ^ 43264256706 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 86528513413) ^ 28842837804 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 86528513413) ^ 7866228492 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 86528513413) ^ 40604652 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 86528513413) ^ 7594884 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_98735663837 : Nat.Prime 98735663837 := by
  apply lucas_primality 98735663837 (2 : ZMod 98735663837)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13687, 1), (1803457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13687, 1), (1803457, 1)] : List FactorBlock).map factorBlockValue).prod) = 98735663837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_13687
      · exact prime_eightyThreeCC_1803457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 98735663837) ^ 49367831918 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 98735663837) ^ 7213828 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 98735663837) ^ 54748 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_123280233431 : Nat.Prime 123280233431 := by
  apply lucas_primality 123280233431 (19 : ZMod 123280233431)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (1949, 1), (134581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (1949, 1), (134581, 1)] : List FactorBlock).map factorBlockValue).prod) = 123280233431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_47
      · exact prime_eightyThreeCC_1949
      · exact prime_eightyThreeCC_134581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 123280233431) ^ 61640116715 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (19 : ZMod 123280233431) ^ 24656046686 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (19 : ZMod 123280233431) ^ 2622983690 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (19 : ZMod 123280233431) ^ 63253070 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (19 : ZMod 123280233431) ^ 916030 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_162228380129 : Nat.Prime 162228380129 := by
  apply lucas_primality 162228380129 (3 : ZMod 162228380129)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5069636879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5069636879, 1)] : List FactorBlock).map factorBlockValue).prod) = 162228380129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5069636879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 162228380129) ^ 81114190064 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 162228380129) ^ 32 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_168208960613 : Nat.Prime 168208960613 := by
  apply lucas_primality 168208960613 (2 : ZMod 168208960613)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (97, 1), (317, 1), (17761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (97, 1), (317, 1), (17761, 1)] : List FactorBlock).map factorBlockValue).prod) = 168208960613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_97
      · exact prime_eightyThreeCC_317
      · exact prime_eightyThreeCC_17761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 168208960613) ^ 84104480306 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 168208960613) ^ 24029851516 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 168208960613) ^ 15291723692 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 168208960613) ^ 1734112996 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 168208960613) ^ 530627636 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 168208960613) ^ 9470692 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_182139249389 : Nat.Prime 182139249389 := by
  apply lucas_primality 182139249389 (2 : ZMod 182139249389)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (3457, 1), (454199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (3457, 1), (454199, 1)] : List FactorBlock).map factorBlockValue).prod) = 182139249389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_29
      · exact prime_eightyThreeCC_3457
      · exact prime_eightyThreeCC_454199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 182139249389) ^ 91069624694 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 182139249389) ^ 6280663772 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 182139249389) ^ 52687084 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 182139249389) ^ 401012 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_212274990463 : Nat.Prime 212274990463 := by
  apply lucas_primality 212274990463 (7 : ZMod 212274990463)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15817, 1), (2236781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15817, 1), (2236781, 1)] : List FactorBlock).map factorBlockValue).prod) = 212274990463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_15817
      · exact prime_eightyThreeCC_2236781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 212274990463) ^ 106137495231 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 212274990463) ^ 70758330154 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 212274990463) ^ 13420686 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 212274990463) ^ 94902 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_220797048959 : Nat.Prime 220797048959 := by
  apply lucas_primality 220797048959 (7 : ZMod 220797048959)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2311, 1), (3907, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2311, 1), (3907, 1), (12227, 1)] : List FactorBlock).map factorBlockValue).prod) = 220797048959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_2311
      · exact prime_eightyThreeCC_3907
      · exact prime_eightyThreeCC_12227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 220797048959) ^ 110398524479 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 220797048959) ^ 95541778 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 220797048959) ^ 56513194 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 220797048959) ^ 18058154 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_247755145403 : Nat.Prime 247755145403 := by
  apply lucas_primality 247755145403 (2 : ZMod 247755145403)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (439, 1), (2030081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (439, 1), (2030081, 1)] : List FactorBlock).map factorBlockValue).prod) = 247755145403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_139
      · exact prime_eightyThreeCC_439
      · exact prime_eightyThreeCC_2030081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 247755145403) ^ 123877572701 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 247755145403) ^ 1782411118 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 247755145403) ^ 564362518 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 247755145403) ^ 122042 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_301716071843 : Nat.Prime 301716071843 := by
  apply lucas_primality 301716071843 (2 : ZMod 301716071843)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1181, 1), (7513973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1181, 1), (7513973, 1)] : List FactorBlock).map factorBlockValue).prod) = 301716071843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_1181
      · exact prime_eightyThreeCC_7513973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 301716071843) ^ 150858035921 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 301716071843) ^ 17748004226 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 301716071843) ^ 255475082 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 301716071843) ^ 40154 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_302466880187 : Nat.Prime 302466880187 := by
  apply lucas_primality 302466880187 (2 : ZMod 302466880187)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (269, 1), (5566397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (269, 1), (5566397, 1)] : List FactorBlock).map factorBlockValue).prod) = 302466880187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_101
      · exact prime_eightyThreeCC_269
      · exact prime_eightyThreeCC_5566397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 302466880187) ^ 151233440093 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 302466880187) ^ 2994721586 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 302466880187) ^ 1124412194 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 302466880187) ^ 54338 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_311948422481 : Nat.Prime 311948422481 := by
  apply lucas_primality 311948422481 (3 : ZMod 311948422481)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (307, 1), (1637, 1), (7759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (307, 1), (1637, 1), (7759, 1)] : List FactorBlock).map factorBlockValue).prod) = 311948422481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_307
      · exact prime_eightyThreeCC_1637
      · exact prime_eightyThreeCC_7759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 311948422481) ^ 155974211240 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 311948422481) ^ 62389684496 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 311948422481) ^ 1016118640 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 311948422481) ^ 190561040 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 311948422481) ^ 40204720 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_355079359571 : Nat.Prime 355079359571 := by
  apply lucas_primality 355079359571 (2 : ZMod 355079359571)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (59, 1), (167, 1), (277213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (59, 1), (167, 1), (277213, 1)] : List FactorBlock).map factorBlockValue).prod) = 355079359571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_59
      · exact prime_eightyThreeCC_167
      · exact prime_eightyThreeCC_277213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 355079359571) ^ 177539679785 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 355079359571) ^ 71015871914 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 355079359571) ^ 27313796890 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 355079359571) ^ 6018294230 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 355079359571) ^ 2126223710 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 355079359571) ^ 1280890 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_385807777241 : Nat.Prime 385807777241 := by
  apply lucas_primality 385807777241 (6 : ZMod 385807777241)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (12781, 1), (754651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (12781, 1), (754651, 1)] : List FactorBlock).map factorBlockValue).prod) = 385807777241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_12781
      · exact prime_eightyThreeCC_754651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 385807777241) ^ 192903888620 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 385807777241) ^ 77161555448 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 385807777241) ^ 30186040 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 385807777241) ^ 511240 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_387970745717 : Nat.Prime 387970745717 := by
  apply lucas_primality 387970745717 (2 : ZMod 387970745717)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (139, 1), (857, 1), (35401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (139, 1), (857, 1), (35401, 1)] : List FactorBlock).map factorBlockValue).prod) = 387970745717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_139
      · exact prime_eightyThreeCC_857
      · exact prime_eightyThreeCC_35401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 387970745717) ^ 193985372858 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 387970745717) ^ 16868293292 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 387970745717) ^ 2791156444 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 387970745717) ^ 452707988 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 387970745717) ^ 10959316 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_603432143687 : Nat.Prime 603432143687 := by
  apply lucas_primality 603432143687 (5 : ZMod 603432143687)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (301716071843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (301716071843, 1)] : List FactorBlock).map factorBlockValue).prod) = 603432143687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_301716071843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 603432143687) ^ 301716071843 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 603432143687) ^ 2 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_624619939303 : Nat.Prime 624619939303 := by
  apply lucas_primality 624619939303 (3 : ZMod 624619939303)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (811, 1), (14262683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (811, 1), (14262683, 1)] : List FactorBlock).map factorBlockValue).prod) = 624619939303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_811
      · exact prime_eightyThreeCC_14262683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 624619939303) ^ 312309969651 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 624619939303) ^ 208206646434 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 624619939303) ^ 770184882 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 624619939303) ^ 43794 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_653075150209 : Nat.Prime 653075150209 := by
  apply lucas_primality 653075150209 (14 : ZMod 653075150209)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (547, 1), (239167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (547, 1), (239167, 1)] : List FactorBlock).map factorBlockValue).prod) = 653075150209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_547
      · exact prime_eightyThreeCC_239167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 653075150209) ^ 326537575104 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (14 : ZMod 653075150209) ^ 217691716736 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (14 : ZMod 653075150209) ^ 50236550016 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (14 : ZMod 653075150209) ^ 1193921664 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (14 : ZMod 653075150209) ^ 2730624 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_694726206311 : Nat.Prime 694726206311 := by
  apply lucas_primality 694726206311 (13 : ZMod 694726206311)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (1567, 1), (2607929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (1567, 1), (2607929, 1)] : List FactorBlock).map factorBlockValue).prod) = 694726206311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_1567
      · exact prime_eightyThreeCC_2607929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 694726206311) ^ 347363103155 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 694726206311) ^ 138945241262 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 694726206311) ^ 40866247430 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 694726206311) ^ 443347930 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 694726206311) ^ 266390 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_877314028361 : Nat.Prime 877314028361 := by
  apply lucas_primality 877314028361 (3 : ZMod 877314028361)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (11, 2), (269, 1), (96263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (11, 2), (269, 1), (96263, 1)] : List FactorBlock).map factorBlockValue).prod) = 877314028361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_269
      · exact prime_eightyThreeCC_96263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 877314028361) ^ 438657014180 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 877314028361) ^ 175462805672 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 877314028361) ^ 125330575480 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 877314028361) ^ 79755820760 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 877314028361) ^ 3261390440 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 877314028361) ^ 9113720 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1090868692843 : Nat.Prime 1090868692843 := by
  apply lucas_primality 1090868692843 (13 : ZMod 1090868692843)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (60603816269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (60603816269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1090868692843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_60603816269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 1090868692843) ^ 545434346421 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 1090868692843) ^ 363622897614 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 1090868692843) ^ 18 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1178048273989 : Nat.Prime 1178048273989 := by
  apply lucas_primality 1178048273989 (6 : ZMod 1178048273989)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13537, 1), (7252027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13537, 1), (7252027, 1)] : List FactorBlock).map factorBlockValue).prod) = 1178048273989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_13537
      · exact prime_eightyThreeCC_7252027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1178048273989) ^ 589024136994 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1178048273989) ^ 392682757996 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1178048273989) ^ 87024324 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1178048273989) ^ 162444 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1575400815487 : Nat.Prime 1575400815487 := by
  apply lucas_primality 1575400815487 (6 : ZMod 1575400815487)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (4606435133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (4606435133, 1)] : List FactorBlock).map factorBlockValue).prod) = 1575400815487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_4606435133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1575400815487) ^ 787700407743 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1575400815487) ^ 525133605162 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1575400815487) ^ 82915832394 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1575400815487) ^ 342 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_2758662066101 : Nat.Prime 2758662066101 := by
  apply lucas_primality 2758662066101 (2 : ZMod 2758662066101)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (683, 1), (40390367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (683, 1), (40390367, 1)] : List FactorBlock).map factorBlockValue).prod) = 2758662066101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_683
      · exact prime_eightyThreeCC_40390367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2758662066101) ^ 1379331033050 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2758662066101) ^ 551732413220 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2758662066101) ^ 4039036700 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2758662066101) ^ 68300 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_2835043679543 : Nat.Prime 2835043679543 := by
  apply lucas_primality 2835043679543 (5 : ZMod 2835043679543)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (443869, 1), (3193559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (443869, 1), (3193559, 1)] : List FactorBlock).map factorBlockValue).prod) = 2835043679543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_443869
      · exact prime_eightyThreeCC_3193559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2835043679543) ^ 1417521839771 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2835043679543) ^ 6387118 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2835043679543) ^ 887738 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_3061836909359 : Nat.Prime 3061836909359 := by
  apply lucas_primality 3061836909359 (7 : ZMod 3061836909359)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (947, 1), (29759, 1), (54323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (947, 1), (29759, 1), (54323, 1)] : List FactorBlock).map factorBlockValue).prod) = 3061836909359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_947
      · exact prime_eightyThreeCC_29759
      · exact prime_eightyThreeCC_54323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3061836909359) ^ 1530918454679 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3061836909359) ^ 3233196314 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3061836909359) ^ 102887762 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3061836909359) ^ 56363546 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_4383265270511 : Nat.Prime 4383265270511 := by
  apply lucas_primality 4383265270511 (21 : ZMod 4383265270511)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (62618075293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (62618075293, 1)] : List FactorBlock).map factorBlockValue).prod) = 4383265270511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_62618075293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 4383265270511) ^ 2191632635255 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (21 : ZMod 4383265270511) ^ 876653054102 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (21 : ZMod 4383265270511) ^ 626180752930 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (21 : ZMod 4383265270511) ^ 70 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_4642159132693 : Nat.Prime 4642159132693 := by
  apply lucas_primality 4642159132693 (6 : ZMod 4642159132693)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (53, 1), (167, 1), (337, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (53, 1), (167, 1), (337, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) = 4642159132693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_53
      · exact prime_eightyThreeCC_167
      · exact prime_eightyThreeCC_337
      · exact prime_eightyThreeCC_2543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4642159132693) ^ 2321079566346 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4642159132693) ^ 1547386377564 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4642159132693) ^ 273068184276 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4642159132693) ^ 87587908164 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4642159132693) ^ 27797360076 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4642159132693) ^ 13774952916 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4642159132693) ^ 1825465644 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5606085856463 : Nat.Prime 5606085856463 := by
  apply lucas_primality 5606085856463 (10 : ZMod 5606085856463)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (13, 1), (167, 1), (3764227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (13, 1), (167, 1), (3764227, 1)] : List FactorBlock).map factorBlockValue).prod) = 5606085856463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_167
      · exact prime_eightyThreeCC_3764227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 5606085856463) ^ 2803042928231 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 5606085856463) ^ 800869408066 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 5606085856463) ^ 431237373574 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 5606085856463) ^ 33569376386 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 5606085856463) ^ 1489306 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5677155812077 : Nat.Prime 5677155812077 := by
  apply lucas_primality 5677155812077 (5 : ZMod 5677155812077)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (211, 1), (223, 1), (1436363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (211, 1), (223, 1), (1436363, 1)] : List FactorBlock).map factorBlockValue).prod) = 5677155812077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_211
      · exact prime_eightyThreeCC_223
      · exact prime_eightyThreeCC_1436363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5677155812077) ^ 2838577906038 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 5677155812077) ^ 1892385270692 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 5677155812077) ^ 811022258868 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 5677155812077) ^ 26905951716 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 5677155812077) ^ 25458097812 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 5677155812077) ^ 3952452 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_8351798049313 : Nat.Prime 8351798049313 := by
  apply lucas_primality 8351798049313 (7 : ZMod 8351798049313)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (34961, 1), (2488427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (34961, 1), (2488427, 1)] : List FactorBlock).map factorBlockValue).prod) = 8351798049313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_34961
      · exact prime_eightyThreeCC_2488427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8351798049313) ^ 4175899024656 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 8351798049313) ^ 2783932683104 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 8351798049313) ^ 238888992 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 8351798049313) ^ 3356256 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_10169999202983 : Nat.Prime 10169999202983 := by
  apply lucas_primality 10169999202983 (5 : ZMod 10169999202983)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (997, 1), (26177, 1), (194839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (997, 1), (26177, 1), (194839, 1)] : List FactorBlock).map factorBlockValue).prod) = 10169999202983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_997
      · exact prime_eightyThreeCC_26177
      · exact prime_eightyThreeCC_194839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10169999202983) ^ 5084999601491 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 10169999202983) ^ 10200601006 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 10169999202983) ^ 388508966 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 10169999202983) ^ 52196938 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_19901747205157 : Nat.Prime 19901747205157 := by
  apply lucas_primality 19901747205157 (2 : ZMod 19901747205157)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (103, 1), (2017, 1), (469589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (103, 1), (2017, 1), (469589, 1)] : List FactorBlock).map factorBlockValue).prod) = 19901747205157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_103
      · exact prime_eightyThreeCC_2017
      · exact prime_eightyThreeCC_469589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19901747205157) ^ 9950873602578 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 19901747205157) ^ 6633915735052 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 19901747205157) ^ 1170691012068 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 19901747205157) ^ 193220846652 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 19901747205157) ^ 9867004068 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 19901747205157) ^ 42381204 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_26109338255591 : Nat.Prime 26109338255591 := by
  apply lucas_primality 26109338255591 (13 : ZMod 26109338255591)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (223, 1), (25439, 1), (460247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (223, 1), (25439, 1), (460247, 1)] : List FactorBlock).map factorBlockValue).prod) = 26109338255591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_223
      · exact prime_eightyThreeCC_25439
      · exact prime_eightyThreeCC_460247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 26109338255591) ^ 13054669127795 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 26109338255591) ^ 5221867651118 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 26109338255591) ^ 117082234330 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 26109338255591) ^ 1026350810 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 26109338255591) ^ 56728970 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_28530626243563 : Nat.Prime 28530626243563 := by
  apply lucas_primality 28530626243563 (11 : ZMod 28530626243563)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (373, 1), (4249423033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (373, 1), (4249423033, 1)] : List FactorBlock).map factorBlockValue).prod) = 28530626243563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_373
      · exact prime_eightyThreeCC_4249423033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 28530626243563) ^ 14265313121781 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 28530626243563) ^ 9510208747854 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 28530626243563) ^ 76489614594 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 28530626243563) ^ 6714 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_31700635636931 : Nat.Prime 31700635636931 := by
  apply lucas_primality 31700635636931 (6 : ZMod 31700635636931)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (1223, 1), (2609, 1), (76423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (1223, 1), (2609, 1), (76423, 1)] : List FactorBlock).map factorBlockValue).prod) = 31700635636931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_1223
      · exact prime_eightyThreeCC_2609
      · exact prime_eightyThreeCC_76423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 31700635636931) ^ 15850317818465 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 31700635636931) ^ 6340127127386 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 31700635636931) ^ 2438510433610 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 31700635636931) ^ 25920388910 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 31700635636931) ^ 12150492770 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 31700635636931) ^ 414804910 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_32060581974247 : Nat.Prime 32060581974247 := by
  apply lucas_primality 32060581974247 (6 : ZMod 32060581974247)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (41, 1), (18618224143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (41, 1), (18618224143, 1)] : List FactorBlock).map factorBlockValue).prod) = 32060581974247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_41
      · exact prime_eightyThreeCC_18618224143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 32060581974247) ^ 16030290987123 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 32060581974247) ^ 10686860658082 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 32060581974247) ^ 4580083139178 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 32060581974247) ^ 781965414006 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 32060581974247) ^ 1722 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_138931474353293 : Nat.Prime 138931474353293 := by
  apply lucas_primality 138931474353293 (2 : ZMod 138931474353293)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (107, 1), (523, 1), (821, 1), (17581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (107, 1), (523, 1), (821, 1), (17581, 1)] : List FactorBlock).map factorBlockValue).prod) = 138931474353293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_43
      · exact prime_eightyThreeCC_107
      · exact prime_eightyThreeCC_523
      · exact prime_eightyThreeCC_821
      · exact prime_eightyThreeCC_17581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 138931474353293) ^ 69465737176646 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 138931474353293) ^ 3230964519844 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 138931474353293) ^ 1298424993956 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 138931474353293) ^ 265643354404 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 138931474353293) ^ 169222258652 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 138931474353293) ^ 7902364732 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_175539642810197 : Nat.Prime 175539642810197 := by
  apply lucas_primality 175539642810197 (3 : ZMod 175539642810197)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (23, 1), (151, 1), (1949, 1), (132313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (23, 1), (151, 1), (1949, 1), (132313, 1)] : List FactorBlock).map factorBlockValue).prod) = 175539642810197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_151
      · exact prime_eightyThreeCC_1949
      · exact prime_eightyThreeCC_132313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 175539642810197) ^ 87769821405098 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 175539642810197) ^ 25077091830028 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 175539642810197) ^ 7632158383052 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 175539642810197) ^ 1162514190796 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 175539642810197) ^ 90066517604 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 175539642810197) ^ 1326699892 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_188782787657999 : Nat.Prime 188782787657999 := by
  apply lucas_primality 188782787657999 (13 : ZMod 188782787657999)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1577119, 1), (59850521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1577119, 1), (59850521, 1)] : List FactorBlock).map factorBlockValue).prod) = 188782787657999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_1577119
      · exact prime_eightyThreeCC_59850521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 188782787657999) ^ 94391393828999 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 188782787657999) ^ 119701042 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 188782787657999) ^ 3154238 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_194316211629853 : Nat.Prime 194316211629853 := by
  apply lucas_primality 194316211629853 (5 : ZMod 194316211629853)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17377, 1), (71681921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17377, 1), (71681921, 1)] : List FactorBlock).map factorBlockValue).prod) = 194316211629853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_17377
      · exact prime_eightyThreeCC_71681921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 194316211629853) ^ 97158105814926 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 194316211629853) ^ 64772070543284 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 194316211629853) ^ 14947400894604 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 194316211629853) ^ 11182379676 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 194316211629853) ^ 2710812 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_223025475004187 : Nat.Prime 223025475004187 := by
  apply lucas_primality 223025475004187 (2 : ZMod 223025475004187)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (79, 1), (139, 1), (350174557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (79, 1), (139, 1), (350174557, 1)] : List FactorBlock).map factorBlockValue).prod) = 223025475004187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_29
      · exact prime_eightyThreeCC_79
      · exact prime_eightyThreeCC_139
      · exact prime_eightyThreeCC_350174557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 223025475004187) ^ 111512737502093 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 223025475004187) ^ 7690533620834 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 223025475004187) ^ 2823107278534 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 223025475004187) ^ 1604499820174 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 223025475004187) ^ 636898 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_297098184492353 : Nat.Prime 297098184492353 := by
  apply lucas_primality 297098184492353 (3 : ZMod 297098184492353)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (4642159132693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (4642159132693, 1)] : List FactorBlock).map factorBlockValue).prod) = 297098184492353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_4642159132693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 297098184492353) ^ 148549092246176 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 297098184492353) ^ 64 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_351259719095447 : Nat.Prime 351259719095447 := by
  apply lucas_primality 351259719095447 (5 : ZMod 351259719095447)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (1090868692843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (1090868692843, 1)] : List FactorBlock).map factorBlockValue).prod) = 351259719095447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_1090868692843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 351259719095447) ^ 175629859547723 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 351259719095447) ^ 50179959870778 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 351259719095447) ^ 15272161699802 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 351259719095447) ^ 322 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_512539847780647 : Nat.Prime 512539847780647 := by
  apply lucas_primality 512539847780647 (3 : ZMod 512539847780647)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (67, 1), (182139249389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (67, 1), (182139249389, 1)] : List FactorBlock).map factorBlockValue).prod) = 512539847780647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_67
      · exact prime_eightyThreeCC_182139249389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 512539847780647) ^ 256269923890323 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 512539847780647) ^ 170846615926882 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 512539847780647) ^ 73219978254378 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 512539847780647) ^ 7649848474338 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 512539847780647) ^ 2814 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_603603075042703 : Nat.Prime 603603075042703 := by
  apply lucas_primality 603603075042703 (5 : ZMod 603603075042703)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (17, 1), (331, 1), (797, 1), (118687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (17, 1), (331, 1), (797, 1), (118687, 1)] : List FactorBlock).map factorBlockValue).prod) = 603603075042703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_331
      · exact prime_eightyThreeCC_797
      · exact prime_eightyThreeCC_118687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 603603075042703) ^ 301801537521351 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 603603075042703) ^ 201201025014234 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 603603075042703) ^ 86229010720386 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 603603075042703) ^ 35506063237806 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 603603075042703) ^ 1823574244842 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 603603075042703) ^ 757343883366 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 603603075042703) ^ 5085671346 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_627673777358387 : Nat.Prime 627673777358387 := by
  apply lucas_primality 627673777358387 (2 : ZMod 627673777358387)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (28530626243563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (28530626243563, 1)] : List FactorBlock).map factorBlockValue).prod) = 627673777358387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_28530626243563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 627673777358387) ^ 313836888679193 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 627673777358387) ^ 57061252487126 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 627673777358387) ^ 22 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_703401813659719 : Nat.Prime 703401813659719 := by
  apply lucas_primality 703401813659719 (6 : ZMod 703401813659719)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (457, 1), (28503193681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (457, 1), (28503193681, 1)] : List FactorBlock).map factorBlockValue).prod) = 703401813659719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_457
      · exact prime_eightyThreeCC_28503193681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 703401813659719) ^ 351700906829859 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 703401813659719) ^ 234467271219906 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 703401813659719) ^ 1539172458774 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 703401813659719) ^ 24678 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_798376077652037 : Nat.Prime 798376077652037 := by
  apply lucas_primality 798376077652037 (2 : ZMod 798376077652037)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (727, 1), (21118825459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (727, 1), (21118825459, 1)] : List FactorBlock).map factorBlockValue).prod) = 798376077652037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_727
      · exact prime_eightyThreeCC_21118825459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 798376077652037) ^ 399188038826018 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 798376077652037) ^ 61413544434772 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 798376077652037) ^ 1098178923868 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 798376077652037) ^ 37804 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1123189937032741 : Nat.Prime 1123189937032741 := by
  apply lucas_primality 1123189937032741 (2 : ZMod 1123189937032741)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (1373, 1), (592793701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (1373, 1), (592793701, 1)] : List FactorBlock).map factorBlockValue).prod) = 1123189937032741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_1373
      · exact prime_eightyThreeCC_592793701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1123189937032741) ^ 561594968516370 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123189937032741) ^ 374396645677580 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123189937032741) ^ 224637987406548 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123189937032741) ^ 48834345088380 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123189937032741) ^ 818055307380 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123189937032741) ^ 1894740 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1152299302152403 : Nat.Prime 1152299302152403 := by
  apply lucas_primality 1152299302152403 (3 : ZMod 1152299302152403)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (227, 1), (3863, 1), (219009767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (227, 1), (3863, 1), (219009767, 1)] : List FactorBlock).map factorBlockValue).prod) = 1152299302152403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_227
      · exact prime_eightyThreeCC_3863
      · exact prime_eightyThreeCC_219009767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1152299302152403) ^ 576149651076201 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1152299302152403) ^ 384099767384134 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1152299302152403) ^ 5076208379526 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1152299302152403) ^ 298291302654 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1152299302152403) ^ 5261406 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1510262301263993 : Nat.Prime 1510262301263993 := by
  apply lucas_primality 1510262301263993 (3 : ZMod 1510262301263993)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (188782787657999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (188782787657999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1510262301263993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_188782787657999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1510262301263993) ^ 755131150631996 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1510262301263993) ^ 8 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1749098787216457 : Nat.Prime 1749098787216457 := by
  apply lucas_primality 1749098787216457 (7 : ZMod 1749098787216457)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (5606085856463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (5606085856463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1749098787216457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_5606085856463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1749098787216457) ^ 874549393608228 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1749098787216457) ^ 583032929072152 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1749098787216457) ^ 134546060555112 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1749098787216457) ^ 312 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1943162116298531 : Nat.Prime 1943162116298531 := by
  apply lucas_primality 1943162116298531 (6 : ZMod 1943162116298531)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (194316211629853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (194316211629853, 1)] : List FactorBlock).map factorBlockValue).prod) = 1943162116298531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_194316211629853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1943162116298531) ^ 971581058149265 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1943162116298531) ^ 388632423259706 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1943162116298531) ^ 10 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1965439409489723 : Nat.Prime 1965439409489723 := by
  apply lucas_primality 1965439409489723 (2 : ZMod 1965439409489723)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (31700635636931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (31700635636931, 1)] : List FactorBlock).map factorBlockValue).prod) = 1965439409489723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_31
      · exact prime_eightyThreeCC_31700635636931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1965439409489723) ^ 982719704744861 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1965439409489723) ^ 63401271273862 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1965439409489723) ^ 62 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_3020524602527987 : Nat.Prime 3020524602527987 := by
  apply lucas_primality 3020524602527987 (2 : ZMod 3020524602527987)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1510262301263993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1510262301263993, 1)] : List FactorBlock).map factorBlockValue).prod) = 3020524602527987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_1510262301263993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3020524602527987) ^ 1510262301263993 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3020524602527987) ^ 2 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_3655578005567809 : Nat.Prime 3655578005567809 := by
  apply lucas_primality 3655578005567809 (7 : ZMod 3655578005567809)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (59, 1), (2099, 1), (153741239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (59, 1), (2099, 1), (153741239, 1)] : List FactorBlock).map factorBlockValue).prod) = 3655578005567809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_59
      · exact prime_eightyThreeCC_2099
      · exact prime_eightyThreeCC_153741239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3655578005567809) ^ 1827789002783904 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3655578005567809) ^ 1218526001855936 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3655578005567809) ^ 61958949246912 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3655578005567809) ^ 1741580755392 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3655578005567809) ^ 23777472 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_4242072133669679 : Nat.Prime 4242072133669679 := by
  apply lucas_primality 4242072133669679 (7 : ZMod 4242072133669679)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (71, 1), (387970745717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (71, 1), (387970745717, 1)] : List FactorBlock).map factorBlockValue).prod) = 4242072133669679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_71
      · exact prime_eightyThreeCC_387970745717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4242072133669679) ^ 2121036066834839 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4242072133669679) ^ 606010304809954 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4242072133669679) ^ 385642921242698 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4242072133669679) ^ 59747494840418 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4242072133669679) ^ 10934 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5018022318062657 : Nat.Prime 5018022318062657 := by
  apply lucas_primality 5018022318062657 (3 : ZMod 5018022318062657)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (347, 1), (59053, 1), (546617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (347, 1), (59053, 1), (546617, 1)] : List FactorBlock).map factorBlockValue).prod) = 5018022318062657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_347
      · exact prime_eightyThreeCC_59053
      · exact prime_eightyThreeCC_546617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5018022318062657) ^ 2509011159031328 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5018022318062657) ^ 716860331151808 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5018022318062657) ^ 14461159418048 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5018022318062657) ^ 84974892352 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5018022318062657) ^ 9180143168 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5081772263415073 : Nat.Prime 5081772263415073 := by
  apply lucas_primality 5081772263415073 (10 : ZMod 5081772263415073)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (157, 1), (1489, 1), (3709, 1), (61051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (157, 1), (1489, 1), (3709, 1), (61051, 1)] : List FactorBlock).map factorBlockValue).prod) = 5081772263415073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_157
      · exact prime_eightyThreeCC_1489
      · exact prime_eightyThreeCC_3709
      · exact prime_eightyThreeCC_61051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 5081772263415073) ^ 2540886131707536 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 5081772263415073) ^ 1693924087805024 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 5081772263415073) ^ 32367976200096 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 5081772263415073) ^ 3412875932448 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 5081772263415073) ^ 1370119240608 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 5081772263415073) ^ 83238149472 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5309210678451371 : Nat.Prime 5309210678451371 := by
  apply lucas_primality 5309210678451371 (6 : ZMod 5309210678451371)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (6491, 1), (3556235509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (6491, 1), (3556235509, 1)] : List FactorBlock).map factorBlockValue).prod) = 5309210678451371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_6491
      · exact prime_eightyThreeCC_3556235509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5309210678451371) ^ 2654605339225685 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5309210678451371) ^ 1061842135690274 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5309210678451371) ^ 230835246889190 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5309210678451371) ^ 817934167070 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5309210678451371) ^ 1492930 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_8333894000575393 : Nat.Prime 8333894000575393 := by
  apply lucas_primality 8333894000575393 (5 : ZMod 8333894000575393)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (16193, 1), (315355567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (16193, 1), (315355567, 1)] : List FactorBlock).map factorBlockValue).prod) = 8333894000575393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_16193
      · exact prime_eightyThreeCC_315355567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8333894000575393) ^ 4166947000287696 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 8333894000575393) ^ 2777964666858464 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 8333894000575393) ^ 490229058857376 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 8333894000575393) ^ 514660285344 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 8333894000575393) ^ 26426976 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_12738588214319369 : Nat.Prime 12738588214319369 := by
  apply lucas_primality 12738588214319369 (3 : ZMod 12738588214319369)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (79, 1), (103, 1), (8819, 1), (22189507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (79, 1), (103, 1), (8819, 1), (22189507, 1)] : List FactorBlock).map factorBlockValue).prod) = 12738588214319369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_79
      · exact prime_eightyThreeCC_103
      · exact prime_eightyThreeCC_8819
      · exact prime_eightyThreeCC_22189507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12738588214319369) ^ 6369294107159684 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12738588214319369) ^ 161247952079992 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12738588214319369) ^ 123675613731256 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12738588214319369) ^ 1444448147672 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12738588214319369) ^ 574081624 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_16813717834405993 : Nat.Prime 16813717834405993 := by
  apply lucas_primality 16813717834405993 (5 : ZMod 16813717834405993)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1973, 1), (355079359571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1973, 1), (355079359571, 1)] : List FactorBlock).map factorBlockValue).prod) = 16813717834405993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_1973
      · exact prime_eightyThreeCC_355079359571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16813717834405993) ^ 8406858917202996 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 16813717834405993) ^ 5604572611468664 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 16813717834405993) ^ 8521904629704 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 16813717834405993) ^ 47352 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_28976943930708593 : Nat.Prime 28976943930708593 := by
  apply lucas_primality 28976943930708593 (3 : ZMod 28976943930708593)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 1), (19901747205157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 1), (19901747205157, 1)] : List FactorBlock).map factorBlockValue).prod) = 28976943930708593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_19901747205157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28976943930708593) ^ 14488471965354296 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 28976943930708593) ^ 4139563418672656 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 28976943930708593) ^ 2228995686977584 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 28976943930708593) ^ 1456 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_32734379685137833 : Nat.Prime 32734379685137833 := by
  apply lucas_primality 32734379685137833 (10 : ZMod 32734379685137833)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 2), (4519, 1), (595309171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 2), (4519, 1), (595309171, 1)] : List FactorBlock).map factorBlockValue).prod) = 32734379685137833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_4519
      · exact prime_eightyThreeCC_595309171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32734379685137833) ^ 16367189842568916 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 32734379685137833) ^ 10911459895045944 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 32734379685137833) ^ 2518029206549064 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 32734379685137833) ^ 7243721992728 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 32734379685137833) ^ 54987192 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_39320663412920047 : Nat.Prime 39320663412920047 := by
  apply lucas_primality 39320663412920047 (5 : ZMod 39320663412920047)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (251, 1), (26109338255591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (251, 1), (26109338255591, 1)] : List FactorBlock).map factorBlockValue).prod) = 39320663412920047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_251
      · exact prime_eightyThreeCC_26109338255591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 39320663412920047) ^ 19660331706460023 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 39320663412920047) ^ 13106887804306682 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 39320663412920047) ^ 156656029533546 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 39320663412920047) ^ 1506 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_51495205593263863 : Nat.Prime 51495205593263863 := by
  apply lucas_primality 51495205593263863 (5 : ZMod 51495205593263863)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (751, 1), (881, 1), (12971783767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (751, 1), (881, 1), (12971783767, 1)] : List FactorBlock).map factorBlockValue).prod) = 51495205593263863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_751
      · exact prime_eightyThreeCC_881
      · exact prime_eightyThreeCC_12971783767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 51495205593263863) ^ 25747602796631931 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 51495205593263863) ^ 17165068531087954 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 51495205593263863) ^ 68568848992362 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 51495205593263863) ^ 58450857654102 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 51495205593263863) ^ 3969786 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_53663436198976381 : Nat.Prime 53663436198976381 := by
  apply lucas_primality 53663436198976381 (13 : ZMod 53663436198976381)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (385943, 1), (331059473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (385943, 1), (331059473, 1)] : List FactorBlock).map factorBlockValue).prod) = 53663436198976381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_385943
      · exact prime_eightyThreeCC_331059473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 53663436198976381) ^ 26831718099488190 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 53663436198976381) ^ 17887812066325460 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 53663436198976381) ^ 10732687239795276 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 53663436198976381) ^ 7666205171282340 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 53663436198976381) ^ 139044978660 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 53663436198976381) ^ 162096060 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_62287736819661433 : Nat.Prime 62287736819661433 := by
  apply lucas_primality 62287736819661433 (5 : ZMod 62287736819661433)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (37, 1), (307, 1), (25386843203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (37, 1), (307, 1), (25386843203, 1)] : List FactorBlock).map factorBlockValue).prod) = 62287736819661433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_37
      · exact prime_eightyThreeCC_307
      · exact prime_eightyThreeCC_25386843203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 62287736819661433) ^ 31143868409830716 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 62287736819661433) ^ 20762578939887144 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 62287736819661433) ^ 1683452346477336 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 62287736819661433) ^ 202891650878376 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 62287736819661433) ^ 2453544 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_69137958129144181 : Nat.Prime 69137958129144181 := by
  apply lucas_primality 69137958129144181 (10 : ZMod 69137958129144181)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1152299302152403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1152299302152403, 1)] : List FactorBlock).map factorBlockValue).prod) = 69137958129144181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_1152299302152403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 69137958129144181) ^ 34568979064572090 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 69137958129144181) ^ 23045986043048060 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 69137958129144181) ^ 13827591625828836 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 69137958129144181) ^ 60 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_74467270253365049 : Nat.Prime 74467270253365049 := by
  apply lucas_primality 74467270253365049 (3 : ZMod 74467270253365049)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (138931474353293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (138931474353293, 1)] : List FactorBlock).map factorBlockValue).prod) = 74467270253365049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_67
      · exact prime_eightyThreeCC_138931474353293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 74467270253365049) ^ 37233635126682524 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 74467270253365049) ^ 1111451794826344 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 74467270253365049) ^ 536 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_153822099989146469 : Nat.Prime 153822099989146469 := by
  apply lucas_primality 153822099989146469 (2 : ZMod 153822099989146469)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (43, 1), (383, 1), (212274990463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (43, 1), (383, 1), (212274990463, 1)] : List FactorBlock).map factorBlockValue).prod) = 153822099989146469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_43
      · exact prime_eightyThreeCC_383
      · exact prime_eightyThreeCC_212274990463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 153822099989146469) ^ 76911049994573234 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 153822099989146469) ^ 13983827271740588 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 153822099989146469) ^ 3577258139282476 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 153822099989146469) ^ 401624281955996 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 153822099989146469) ^ 724636 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_157100574615074501 : Nat.Prime 157100574615074501 := by
  apply lucas_primality 157100574615074501 (3 : ZMod 157100574615074501)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (1051, 1), (2909, 1), (6983, 1), (14717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (1051, 1), (2909, 1), (6983, 1), (14717, 1)] : List FactorBlock).map factorBlockValue).prod) = 157100574615074501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_1051
      · exact prime_eightyThreeCC_2909
      · exact prime_eightyThreeCC_6983
      · exact prime_eightyThreeCC_14717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 157100574615074501) ^ 78550287307537250 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 157100574615074501) ^ 31420114923014900 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 157100574615074501) ^ 149477235599500 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 157100574615074501) ^ 54005010180500 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 157100574615074501) ^ 22497576201500 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 157100574615074501) ^ 10674768948500 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_335247922940194267 : Nat.Prime 335247922940194267 := by
  apply lucas_primality 335247922940194267 (2 : ZMod 335247922940194267)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3049, 1), (45673, 1), (401234143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3049, 1), (45673, 1), (401234143, 1)] : List FactorBlock).map factorBlockValue).prod) = 335247922940194267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_3049
      · exact prime_eightyThreeCC_45673
      · exact prime_eightyThreeCC_401234143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 335247922940194267) ^ 167623961470097133 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 335247922940194267) ^ 111749307646731422 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 335247922940194267) ^ 109953402079434 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 335247922940194267) ^ 7340177412042 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 335247922940194267) ^ 835541862 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_452746456823018447 : Nat.Prime 452746456823018447 := by
  apply lucas_primality 452746456823018447 (5 : ZMod 452746456823018447)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2713, 1), (1393261, 1), (5444401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2713, 1), (1393261, 1), (5444401, 1)] : List FactorBlock).map factorBlockValue).prod) = 452746456823018447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_2713
      · exact prime_eightyThreeCC_1393261
      · exact prime_eightyThreeCC_5444401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 452746456823018447) ^ 226373228411509223 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 452746456823018447) ^ 41158768802092586 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 452746456823018447) ^ 166880374796542 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 452746456823018447) ^ 324954518086 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 452746456823018447) ^ 83158176046 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_519004825871237323 : Nat.Prime 519004825871237323 := by
  apply lucas_primality 519004825871237323 (3 : ZMod 519004825871237323)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (1613, 1), (385807777241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (1613, 1), (385807777241, 1)] : List FactorBlock).map factorBlockValue).prod) = 519004825871237323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_139
      · exact prime_eightyThreeCC_1613
      · exact prime_eightyThreeCC_385807777241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 519004825871237323) ^ 259502412935618661 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 519004825871237323) ^ 173001608623745774 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 519004825871237323) ^ 3733847668138398 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 519004825871237323) ^ 321763686218994 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 519004825871237323) ^ 1345242 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_599511034433268149 : Nat.Prime 599511034433268149 := by
  apply lucas_primality 599511034433268149 (2 : ZMod 599511034433268149)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (4418941, 1), (128962439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (4418941, 1), (128962439, 1)] : List FactorBlock).map factorBlockValue).prod) = 599511034433268149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_263
      · exact prime_eightyThreeCC_4418941
      · exact prime_eightyThreeCC_128962439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 599511034433268149) ^ 299755517216634074 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 599511034433268149) ^ 2279509636628396 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 599511034433268149) ^ 135668485828 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 599511034433268149) ^ 4648725932 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_608393681750216233 : Nat.Prime 608393681750216233 := by
  apply lucas_primality 608393681750216233 (5 : ZMod 608393681750216233)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (103, 1), (16267, 1), (387939637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (103, 1), (16267, 1), (387939637, 1)] : List FactorBlock).map factorBlockValue).prod) = 608393681750216233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_103
      · exact prime_eightyThreeCC_16267
      · exact prime_eightyThreeCC_387939637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 608393681750216233) ^ 304196840875108116 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 608393681750216233) ^ 202797893916738744 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 608393681750216233) ^ 46799513980785864 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 608393681750216233) ^ 5906734774273944 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 608393681750216233) ^ 37400484523896 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 608393681750216233) ^ 1568268936 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_753984962256915679 : Nat.Prime 753984962256915679 := by
  apply lucas_primality 753984962256915679 (3 : ZMod 753984962256915679)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (180883, 1), (694726206311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (180883, 1), (694726206311, 1)] : List FactorBlock).map factorBlockValue).prod) = 753984962256915679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_180883
      · exact prime_eightyThreeCC_694726206311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 753984962256915679) ^ 376992481128457839 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 753984962256915679) ^ 251328320752305226 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 753984962256915679) ^ 4168357237866 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 753984962256915679) ^ 1085298 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_940636052248999993 : Nat.Prime 940636052248999993 := by
  apply lucas_primality 940636052248999993 (5 : ZMod 940636052248999993)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3407, 1), (116189, 1), (99008671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3407, 1), (116189, 1), (99008671, 1)] : List FactorBlock).map factorBlockValue).prod) = 940636052248999993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_3407
      · exact prime_eightyThreeCC_116189
      · exact prime_eightyThreeCC_99008671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 940636052248999993) ^ 470318026124499996 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 940636052248999993) ^ 313545350749666664 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 940636052248999993) ^ 276089243395656 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 940636052248999993) ^ 8095741010328 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 940636052248999993) ^ 9500542152 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_996773118834235711 : Nat.Prime 996773118834235711 := by
  apply lucas_primality 996773118834235711 (3 : ZMod 996773118834235711)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (3020524602527987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (3020524602527987, 1)] : List FactorBlock).map factorBlockValue).prod) = 996773118834235711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_3020524602527987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 996773118834235711) ^ 498386559417117855 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 996773118834235711) ^ 332257706278078570 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 996773118834235711) ^ 199354623766847142 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 996773118834235711) ^ 90615738075839610 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 996773118834235711) ^ 330 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1070673581210967931 : Nat.Prime 1070673581210967931 := by
  apply lucas_primality 1070673581210967931 (3 : ZMod 1070673581210967931)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (29, 1), (151, 1), (1031, 1), (2029, 1), (556573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (29, 1), (151, 1), (1031, 1), (2029, 1), (556573, 1)] : List FactorBlock).map factorBlockValue).prod) = 1070673581210967931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_29
      · exact prime_eightyThreeCC_151
      · exact prime_eightyThreeCC_1031
      · exact prime_eightyThreeCC_2029
      · exact prime_eightyThreeCC_556573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1070673581210967931) ^ 535336790605483965 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070673581210967931) ^ 356891193736989310 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070673581210967931) ^ 214134716242193586 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070673581210967931) ^ 152953368744423990 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070673581210967931) ^ 36919778662447170 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070673581210967931) ^ 7090553517953430 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070673581210967931) ^ 1038480680127030 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070673581210967931) ^ 527685352987170 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070673581210967931) ^ 1923689401410 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1134055671477554053 : Nat.Prime 1134055671477554053 := by
  apply lucas_primality 1134055671477554053 (2 : ZMod 1134055671477554053)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (151, 1), (2366669, 1), (29383001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (151, 1), (2366669, 1), (29383001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1134055671477554053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_151
      · exact prime_eightyThreeCC_2366669
      · exact prime_eightyThreeCC_29383001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1134055671477554053) ^ 567027835738777026 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1134055671477554053) ^ 378018557159184684 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1134055671477554053) ^ 7510302460116252 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1134055671477554053) ^ 479177980308 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1134055671477554053) ^ 38595638052 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1833950160543826711 : Nat.Prime 1833950160543826711 := by
  apply lucas_primality 1833950160543826711 (3 : ZMod 1833950160543826711)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (7, 2), (11, 1), (139, 1), (10073437357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (7, 2), (11, 1), (139, 1), (10073437357, 1)] : List FactorBlock).map factorBlockValue).prod) = 1833950160543826711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_139
      · exact prime_eightyThreeCC_10073437357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1833950160543826711) ^ 916975080271913355 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1833950160543826711) ^ 611316720181275570 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1833950160543826711) ^ 366790032108765342 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1833950160543826711) ^ 261992880077689530 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1833950160543826711) ^ 166722741867620610 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1833950160543826711) ^ 13193886047077890 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1833950160543826711) ^ 182058030 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_2070750052023220591 : Nat.Prime 2070750052023220591 := by
  apply lucas_primality 2070750052023220591 (3 : ZMod 2070750052023220591)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (4933, 1), (22067, 1), (2506291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (4933, 1), (22067, 1), (2506291, 1)] : List FactorBlock).map factorBlockValue).prod) = 2070750052023220591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_4933
      · exact prime_eightyThreeCC_22067
      · exact prime_eightyThreeCC_2506291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2070750052023220591) ^ 1035375026011610295 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2070750052023220591) ^ 690250017341073530 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2070750052023220591) ^ 414150010404644118 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2070750052023220591) ^ 188250004729383690 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2070750052023220591) ^ 90032610957531330 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2070750052023220591) ^ 419774995342230 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2070750052023220591) ^ 93839219287770 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2070750052023220591) ^ 826220918490 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_2425012987017290177 : Nat.Prime 2425012987017290177 := by
  apply lucas_primality 2425012987017290177 (3 : ZMod 2425012987017290177)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (23, 1), (199, 1), (16369, 1), (38903411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (23, 1), (199, 1), (16369, 1), (38903411, 1)] : List FactorBlock).map factorBlockValue).prod) = 2425012987017290177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_199
      · exact prime_eightyThreeCC_16369
      · exact prime_eightyThreeCC_38903411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2425012987017290177) ^ 1212506493508645088 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2425012987017290177) ^ 186539460539791552 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2425012987017290177) ^ 105435347261621312 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2425012987017290177) ^ 12185994909634624 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2425012987017290177) ^ 148146678906304 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2425012987017290177) ^ 62334199616 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_3114028955227423939 : Nat.Prime 3114028955227423939 := by
  apply lucas_primality 3114028955227423939 (2 : ZMod 3114028955227423939)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (519004825871237323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (519004825871237323, 1)] : List FactorBlock).map factorBlockValue).prod) = 3114028955227423939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_519004825871237323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3114028955227423939) ^ 1557014477613711969 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3114028955227423939) ^ 1038009651742474646 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3114028955227423939) ^ 6 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_4173434291030671019 : Nat.Prime 4173434291030671019 := by
  apply lucas_primality 4173434291030671019 (2 : ZMod 4173434291030671019)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (127493, 1), (24392410703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (127493, 1), (24392410703, 1)] : List FactorBlock).map factorBlockValue).prod) = 4173434291030671019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_61
      · exact prime_eightyThreeCC_127493
      · exact prime_eightyThreeCC_24392410703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4173434291030671019) ^ 2086717145515335509 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4173434291030671019) ^ 379403117366424638 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4173434291030671019) ^ 68416955590666738 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4173434291030671019) ^ 32734615163426 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4173434291030671019) ^ 171095606 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_4737031733221980887 : Nat.Prime 4737031733221980887 := by
  apply lucas_primality 4737031733221980887 (5 : ZMod 4737031733221980887)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (1277, 1), (8179, 1), (11411, 1), (336829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (1277, 1), (8179, 1), (11411, 1), (336829, 1)] : List FactorBlock).map factorBlockValue).prod) = 4737031733221980887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_59
      · exact prime_eightyThreeCC_1277
      · exact prime_eightyThreeCC_8179
      · exact prime_eightyThreeCC_11411
      · exact prime_eightyThreeCC_336829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4737031733221980887) ^ 2368515866610990443 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4737031733221980887) ^ 80288673444440354 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4737031733221980887) ^ 3709500182632718 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4737031733221980887) ^ 579170037073234 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4737031733221980887) ^ 415128536782226 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4737031733221980887) ^ 14063610120334 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_11953685497077283747 : Nat.Prime 11953685497077283747 := by
  apply lucas_primality 11953685497077283747 (5 : ZMod 11953685497077283747)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (337, 1), (2143, 1), (2758662066101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (337, 1), (2143, 1), (2758662066101, 1)] : List FactorBlock).map factorBlockValue).prod) = 11953685497077283747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_337
      · exact prime_eightyThreeCC_2143
      · exact prime_eightyThreeCC_2758662066101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11953685497077283747) ^ 5976842748538641873 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11953685497077283747) ^ 3984561832359094582 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11953685497077283747) ^ 35470876845926658 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11953685497077283747) ^ 5578014697656222 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 11953685497077283747) ^ 4333146 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_12305767999131717521 : Nat.Prime 12305767999131717521 := by
  apply lucas_primality 12305767999131717521 (3 : ZMod 12305767999131717521)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (153822099989146469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (153822099989146469, 1)] : List FactorBlock).map factorBlockValue).prod) = 12305767999131717521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_153822099989146469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12305767999131717521) ^ 6152883999565858760 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12305767999131717521) ^ 2461153599826343504 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12305767999131717521) ^ 80 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_21391270505312129099 : Nat.Prime 21391270505312129099 := by
  apply lucas_primality 21391270505312129099 (2 : ZMod 21391270505312129099)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1087, 1), (2858467, 1), (3442261481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1087, 1), (2858467, 1), (3442261481, 1)] : List FactorBlock).map factorBlockValue).prod) = 21391270505312129099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_1087
      · exact prime_eightyThreeCC_2858467
      · exact prime_eightyThreeCC_3442261481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21391270505312129099) ^ 10695635252656064549 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21391270505312129099) ^ 19679181697619254 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21391270505312129099) ^ 7483476459694 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21391270505312129099) ^ 6214307258 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_24336561261458751713 : Nat.Prime 24336561261458751713 := by
  apply lucas_primality 24336561261458751713 (3 : ZMod 24336561261458751713)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (69137958129144181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (69137958129144181, 1)] : List FactorBlock).map factorBlockValue).prod) = 24336561261458751713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_69137958129144181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 24336561261458751713) ^ 12168280630729375856 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 24336561261458751713) ^ 2212414660132613792 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 24336561261458751713) ^ 352 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_46674950617554267451 : Nat.Prime 46674950617554267451 := by
  apply lucas_primality 46674950617554267451 (3 : ZMod 46674950617554267451)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 1), (113, 1), (1627, 1), (80317, 1), (1620973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 1), (113, 1), (1627, 1), (80317, 1), (1620973, 1)] : List FactorBlock).map factorBlockValue).prod) = 46674950617554267451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_113
      · exact prime_eightyThreeCC_1627
      · exact prime_eightyThreeCC_80317
      · exact prime_eightyThreeCC_1620973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46674950617554267451) ^ 23337475308777133725 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46674950617554267451) ^ 15558316872518089150 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46674950617554267451) ^ 9334990123510853490 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46674950617554267451) ^ 3590380816734943650 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46674950617554267451) ^ 413052660332338650 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46674950617554267451) ^ 28687738547974350 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46674950617554267451) ^ 581134138694850 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46674950617554267451) ^ 28794403495650 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_54746837985859449049 : Nat.Prime 54746837985859449049 := by
  apply lucas_primality 54746837985859449049 (17 : ZMod 54746837985859449049)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (181, 1), (503, 1), (8351798049313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (181, 1), (503, 1), (8351798049313, 1)] : List FactorBlock).map factorBlockValue).prod) = 54746837985859449049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_181
      · exact prime_eightyThreeCC_503
      · exact prime_eightyThreeCC_8351798049313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 54746837985859449049) ^ 27373418992929724524 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 54746837985859449049) ^ 18248945995286483016 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 54746837985859449049) ^ 302468718153919608 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 54746837985859449049) ^ 108840632178647016 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 54746837985859449049) ^ 6555096 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_57388213270765035199 : Nat.Prime 57388213270765035199 := by
  apply lucas_primality 57388213270765035199 (6 : ZMod 57388213270765035199)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4783, 1), (5407, 1), (123280233431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4783, 1), (5407, 1), (123280233431, 1)] : List FactorBlock).map factorBlockValue).prod) = 57388213270765035199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_4783
      · exact prime_eightyThreeCC_5407
      · exact prime_eightyThreeCC_123280233431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 57388213270765035199) ^ 28694106635382517599 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 57388213270765035199) ^ 19129404423588345066 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 57388213270765035199) ^ 11998371998905506 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 57388213270765035199) ^ 10613688417008514 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 57388213270765035199) ^ 465510258 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_64897336524599726681 : Nat.Prime 64897336524599726681 := by
  apply lucas_primality 64897336524599726681 (3 : ZMod 64897336524599726681)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (83, 1), (97, 1), (157, 1), (98735663837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (83, 1), (97, 1), (157, 1), (98735663837, 1)] : List FactorBlock).map factorBlockValue).prod) = 64897336524599726681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_83
      · exact prime_eightyThreeCC_97
      · exact prime_eightyThreeCC_157
      · exact prime_eightyThreeCC_98735663837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64897336524599726681) ^ 32448668262299863340 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 64897336524599726681) ^ 12979467304919945336 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 64897336524599726681) ^ 4992102809584594360 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 64897336524599726681) ^ 781895620778309960 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 64897336524599726681) ^ 669044706439172440 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 64897336524599726681) ^ 413358831366877240 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 64897336524599726681) ^ 657283640 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_66447812881572484337 : Nat.Prime 66447812881572484337 := by
  apply lucas_primality 66447812881572484337 (3 : ZMod 66447812881572484337)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (19, 1), (16813717834405993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (19, 1), (16813717834405993, 1)] : List FactorBlock).map factorBlockValue).prod) = 66447812881572484337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_16813717834405993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66447812881572484337) ^ 33223906440786242168 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 66447812881572484337) ^ 5111370221659421872 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 66447812881572484337) ^ 3497253309556446544 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 66447812881572484337) ^ 3952 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_78895040467151968883 : Nat.Prime 78895040467151968883 := by
  apply lucas_primality 78895040467151968883 (2 : ZMod 78895040467151968883)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (112303, 1), (351259719095447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (112303, 1), (351259719095447, 1)] : List FactorBlock).map factorBlockValue).prod) = 78895040467151968883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_112303
      · exact prime_eightyThreeCC_351259719095447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 78895040467151968883) ^ 39447520233575984441 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 78895040467151968883) ^ 702519438190894 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 78895040467151968883) ^ 224606 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_120099884573592689663 : Nat.Prime 120099884573592689663 := by
  apply lucas_primality 120099884573592689663 (5 : ZMod 120099884573592689663)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (223, 1), (443, 1), (34171, 1), (1368368173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (223, 1), (443, 1), (34171, 1), (1368368173, 1)] : List FactorBlock).map factorBlockValue).prod) = 120099884573592689663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_223
      · exact prime_eightyThreeCC_443
      · exact prime_eightyThreeCC_34171
      · exact prime_eightyThreeCC_1368368173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 120099884573592689663) ^ 60049942286796344831 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 120099884573592689663) ^ 9238452659507129974 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 120099884573592689663) ^ 538564504814316994 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 120099884573592689663) ^ 271105834251902234 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 120099884573592689663) ^ 3514672809504922 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 120099884573592689663) ^ 87768691894 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_176926906264229381737 : Nat.Prime 176926906264229381737 := by
  apply lucas_primality 176926906264229381737 (17 : ZMod 176926906264229381737)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (19, 1), (27893, 1), (220797048959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (19, 1), (27893, 1), (220797048959, 1)] : List FactorBlock).map factorBlockValue).prod) = 176926906264229381737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_27893
      · exact prime_eightyThreeCC_220797048959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 176926906264229381737) ^ 88463453132114690868 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 176926906264229381737) ^ 58975635421409793912 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 176926906264229381737) ^ 25275272323461340248 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 176926906264229381737) ^ 9311942434959441144 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 176926906264229381737) ^ 6343057622494152 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (17 : ZMod 176926906264229381737) ^ 801310104 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_234787534371065591021 : Nat.Prime 234787534371065591021 := by
  apply lucas_primality 234787534371065591021 (10 : ZMod 234787534371065591021)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (140970721, 1), (11896469033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (140970721, 1), (11896469033, 1)] : List FactorBlock).map factorBlockValue).prod) = 234787534371065591021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_140970721
      · exact prime_eightyThreeCC_11896469033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 234787534371065591021) ^ 117393767185532795510 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 234787534371065591021) ^ 46957506874213118204 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 234787534371065591021) ^ 33541076338723655860 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 234787534371065591021) ^ 1665505664620 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (10 : ZMod 234787534371065591021) ^ 19735900940 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_361739576058350048219 : Nat.Prime 361739576058350048219 := by
  apply lucas_primality 361739576058350048219 (6 : ZMod 361739576058350048219)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (163, 1), (661, 1), (9173, 1), (16636918421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (163, 1), (661, 1), (9173, 1), (16636918421, 1)] : List FactorBlock).map factorBlockValue).prod) = 361739576058350048219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_163
      · exact prime_eightyThreeCC_661
      · exact prime_eightyThreeCC_9173
      · exact prime_eightyThreeCC_16636918421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 361739576058350048219) ^ 180869788029175024109 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 361739576058350048219) ^ 32885416005304549838 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 361739576058350048219) ^ 2219261202811963486 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 361739576058350048219) ^ 547261083295537138 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 361739576058350048219) ^ 39435253031543666 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (6 : ZMod 361739576058350048219) ^ 21743183858 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_619700922902133969899 : Nat.Prime 619700922902133969899 := by
  apply lucas_primality 619700922902133969899 (2 : ZMod 619700922902133969899)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (37, 1), (28976943930708593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (37, 1), (28976943930708593, 1)] : List FactorBlock).map factorBlockValue).prod) = 619700922902133969899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_37
      · exact prime_eightyThreeCC_28976943930708593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 619700922902133969899) ^ 309850461451066984949 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 619700922902133969899) ^ 36452995464831409994 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 619700922902133969899) ^ 16748673591949566754 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 619700922902133969899) ^ 21386 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_691913010381635377421 : Nat.Prime 691913010381635377421 := by
  apply lucas_primality 691913010381635377421 (3 : ZMod 691913010381635377421)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (307, 1), (1223, 1), (865003, 1), (106521937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (307, 1), (1223, 1), (865003, 1), (106521937, 1)] : List FactorBlock).map factorBlockValue).prod) = 691913010381635377421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_307
      · exact prime_eightyThreeCC_1223
      · exact prime_eightyThreeCC_865003
      · exact prime_eightyThreeCC_106521937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 691913010381635377421) ^ 345956505190817688710 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 691913010381635377421) ^ 138382602076327075484 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 691913010381635377421) ^ 2253788307432037060 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 691913010381635377421) ^ 565750621734779540 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 691913010381635377421) ^ 799896659759140 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 691913010381635377421) ^ 6495497827660 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1036580929578397992287 : Nat.Prime 1036580929578397992287 := by
  apply lucas_primality 1036580929578397992287 (5 : ZMod 1036580929578397992287)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (29, 1), (940636052248999993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (29, 1), (940636052248999993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1036580929578397992287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_29
      · exact prime_eightyThreeCC_940636052248999993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1036580929578397992287) ^ 518290464789198996143 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1036580929578397992287) ^ 54556891030441999594 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1036580929578397992287) ^ 35744169985461999734 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1036580929578397992287) ^ 1102 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1047035690201412119597 : Nat.Prime 1047035690201412119597 := by
  apply lucas_primality 1047035690201412119597 (2 : ZMod 1047035690201412119597)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (491, 1), (3037, 1), (175539642810197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (491, 1), (3037, 1), (175539642810197, 1)] : List FactorBlock).map factorBlockValue).prod) = 1047035690201412119597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_491
      · exact prime_eightyThreeCC_3037
      · exact prime_eightyThreeCC_175539642810197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1047035690201412119597) ^ 523517845100706059798 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1047035690201412119597) ^ 2132455580858273156 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1047035690201412119597) ^ 344759858479226908 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1047035690201412119597) ^ 5964668 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1323163021670647926607 : Nat.Prime 1323163021670647926607 := by
  apply lucas_primality 1323163021670647926607 (3 : ZMod 1323163021670647926607)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (425538493, 1), (5956676311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (425538493, 1), (5956676311, 1)] : List FactorBlock).map factorBlockValue).prod) = 1323163021670647926607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_29
      · exact prime_eightyThreeCC_425538493
      · exact prime_eightyThreeCC_5956676311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1323163021670647926607) ^ 661581510835323963303 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1323163021670647926607) ^ 441054340556882642202 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1323163021670647926607) ^ 45626311092091307814 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1323163021670647926607) ^ 3109385034342 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1323163021670647926607) ^ 222131093346 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1493406074479103486003 : Nat.Prime 1493406074479103486003 := by
  apply lucas_primality 1493406074479103486003 (2 : ZMod 1493406074479103486003)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (109, 1), (223067167, 1), (626743283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (109, 1), (223067167, 1), (626743283, 1)] : List FactorBlock).map factorBlockValue).prod) = 1493406074479103486003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_109
      · exact prime_eightyThreeCC_223067167
      · exact prime_eightyThreeCC_626743283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1493406074479103486003) ^ 746703037239551743001 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1493406074479103486003) ^ 213343724925586212286 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1493406074479103486003) ^ 13700973160358747578 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1493406074479103486003) ^ 6694871749006 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1493406074479103486003) ^ 2382803477894 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_2316722860720857834997 : Nat.Prime 2316722860720857834997 := by
  apply lucas_primality 2316722860720857834997 (5 : ZMod 2316722860720857834997)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3823, 1), (181499, 1), (505711, 1), (550189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3823, 1), (181499, 1), (505711, 1), (550189, 1)] : List FactorBlock).map factorBlockValue).prod) = 2316722860720857834997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_3823
      · exact prime_eightyThreeCC_181499
      · exact prime_eightyThreeCC_505711
      · exact prime_eightyThreeCC_550189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2316722860720857834997) ^ 1158361430360428917498 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2316722860720857834997) ^ 772240953573619278332 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2316722860720857834997) ^ 605996039947909452 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2316722860720857834997) ^ 12764383609391004 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2316722860720857834997) ^ 4581120166895436 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2316722860720857834997) ^ 4210776407236164 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_2984329991929847958811 : Nat.Prime 2984329991929847958811 := by
  apply lucas_primality 2984329991929847958811 (3 : ZMod 2984329991929847958811)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (4737031733221980887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (4737031733221980887, 1)] : List FactorBlock).map factorBlockValue).prod) = 2984329991929847958811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_4737031733221980887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2984329991929847958811) ^ 1492164995964923979405 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2984329991929847958811) ^ 994776663976615986270 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2984329991929847958811) ^ 596865998385969591762 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2984329991929847958811) ^ 426332855989978279830 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2984329991929847958811) ^ 630 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_3559371709927985201449 : Nat.Prime 3559371709927985201449 := by
  apply lucas_primality 3559371709927985201449 (7 : ZMod 3559371709927985201449)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (140177, 1), (32060581974247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (140177, 1), (32060581974247, 1)] : List FactorBlock).map factorBlockValue).prod) = 3559371709927985201449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_140177
      · exact prime_eightyThreeCC_32060581974247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3559371709927985201449) ^ 1779685854963992600724 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3559371709927985201449) ^ 1186457236642661733816 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3559371709927985201449) ^ 323579246357089563768 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3559371709927985201449) ^ 25391980923603624 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3559371709927985201449) ^ 111020184 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_4118142055560010194763 : Nat.Prime 4118142055560010194763 := by
  apply lucas_primality 4118142055560010194763 (2 : ZMod 4118142055560010194763)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (5231, 1), (13177, 1), (21521, 1), (3281461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (5231, 1), (13177, 1), (21521, 1), (3281461, 1)] : List FactorBlock).map factorBlockValue).prod) = 4118142055560010194763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_47
      · exact prime_eightyThreeCC_5231
      · exact prime_eightyThreeCC_13177
      · exact prime_eightyThreeCC_21521
      · exact prime_eightyThreeCC_3281461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4118142055560010194763) ^ 2059071027780005097381 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4118142055560010194763) ^ 1372714018520003398254 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4118142055560010194763) ^ 87620043735319365846 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4118142055560010194763) ^ 787257131630665302 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4118142055560010194763) ^ 312525009908174106 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4118142055560010194763) ^ 191354586476465322 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4118142055560010194763) ^ 1254972116249442 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_4416239239316667483659 : Nat.Prime 4416239239316667483659 := by
  apply lucas_primality 4416239239316667483659 (2 : ZMod 4416239239316667483659)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (24763, 1), (12738588214319369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (24763, 1), (12738588214319369, 1)] : List FactorBlock).map factorBlockValue).prod) = 4416239239316667483659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_24763
      · exact prime_eightyThreeCC_12738588214319369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4416239239316667483659) ^ 2208119619658333741829 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4416239239316667483659) ^ 630891319902381069094 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4416239239316667483659) ^ 178340235000471166 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4416239239316667483659) ^ 346682 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5627631934154505774923 : Nat.Prime 5627631934154505774923 := by
  apply lucas_primality 5627631934154505774923 (2 : ZMod 5627631934154505774923)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 2), (1231, 1), (3677, 1), (19681, 1), (1132567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 2), (1231, 1), (3677, 1), (19681, 1), (1132567, 1)] : List FactorBlock).map factorBlockValue).prod) = 5627631934154505774923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_167
      · exact prime_eightyThreeCC_1231
      · exact prime_eightyThreeCC_3677
      · exact prime_eightyThreeCC_19681
      · exact prime_eightyThreeCC_1132567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5627631934154505774923) ^ 2813815967077252887461 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5627631934154505774923) ^ 33698394815296441766 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5627631934154505774923) ^ 4571593772668160662 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5627631934154505774923) ^ 1530495494738783186 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5627631934154505774923) ^ 285942377630938762 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5627631934154505774923) ^ 4968917454026566 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_6219485577470387953723 : Nat.Prime 6219485577470387953723 := by
  apply lucas_primality 6219485577470387953723 (2 : ZMod 6219485577470387953723)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1036580929578397992287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1036580929578397992287, 1)] : List FactorBlock).map factorBlockValue).prod) = 6219485577470387953723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_1036580929578397992287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6219485577470387953723) ^ 3109742788735193976861 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6219485577470387953723) ^ 2073161859156795984574 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6219485577470387953723) ^ 6 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_6631858701816355040939 : Nat.Prime 6631858701816355040939 := by
  apply lucas_primality 6631858701816355040939 (2 : ZMod 6631858701816355040939)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (113, 1), (59377, 1), (1046597, 1), (15232367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (113, 1), (59377, 1), (1046597, 1), (15232367, 1)] : List FactorBlock).map factorBlockValue).prod) = 6631858701816355040939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_31
      · exact prime_eightyThreeCC_113
      · exact prime_eightyThreeCC_59377
      · exact prime_eightyThreeCC_1046597
      · exact prime_eightyThreeCC_15232367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6631858701816355040939) ^ 3315929350908177520469 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6631858701816355040939) ^ 213930925865043710998 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6631858701816355040939) ^ 58689015060321726026 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6631858701816355040939) ^ 111690700133323594 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6631858701816355040939) ^ 6336592501045154 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6631858701816355040939) ^ 435379393223414 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_9193891552622435973073 : Nat.Prime 9193891552622435973073 := by
  apply lucas_primality 9193891552622435973073 (13 : ZMod 9193891552622435973073)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (43, 1), (331, 1), (2293, 1), (5779, 1), (92323499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (43, 1), (331, 1), (2293, 1), (5779, 1), (92323499, 1)] : List FactorBlock).map factorBlockValue).prod) = 9193891552622435973073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_43
      · exact prime_eightyThreeCC_331
      · exact prime_eightyThreeCC_2293
      · exact prime_eightyThreeCC_5779
      · exact prime_eightyThreeCC_92323499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 9193891552622435973073) ^ 4596945776311217986536 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 9193891552622435973073) ^ 3064630517540811991024 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 9193891552622435973073) ^ 835808322965675997552 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 9193891552622435973073) ^ 213811431456335720304 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 9193891552622435973073) ^ 27776107409735456112 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 9193891552622435973073) ^ 4009547122818332304 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 9193891552622435973073) ^ 1590913921547401968 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 9193891552622435973073) ^ 99583439234928 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_20687420403272999488643 : Nat.Prime 20687420403272999488643 := by
  apply lucas_primality 20687420403272999488643 (2 : ZMod 20687420403272999488643)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2829569, 1), (3655578005567809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2829569, 1), (3655578005567809, 1)] : List FactorBlock).map factorBlockValue).prod) = 20687420403272999488643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_2829569
      · exact prime_eightyThreeCC_3655578005567809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20687420403272999488643) ^ 10343710201636499744321 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20687420403272999488643) ^ 7311156011135618 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 20687420403272999488643) ^ 5659138 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_26899518244904060525863 : Nat.Prime 26899518244904060525863 := by
  apply lucas_primality 26899518244904060525863 (3 : ZMod 26899518244904060525863)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7369, 1), (608393681750216233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7369, 1), (608393681750216233, 1)] : List FactorBlock).map factorBlockValue).prod) = 26899518244904060525863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7369
      · exact prime_eightyThreeCC_608393681750216233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26899518244904060525863) ^ 13449759122452030262931 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 26899518244904060525863) ^ 8966506081634686841954 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 26899518244904060525863) ^ 3650362090501297398 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 26899518244904060525863) ^ 44214 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_33500257881579753966113 : Nat.Prime 33500257881579753966113 := by
  apply lucas_primality 33500257881579753966113 (3 : ZMod 33500257881579753966113)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (6311, 1), (20219011, 1), (8204272621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (6311, 1), (20219011, 1), (8204272621, 1)] : List FactorBlock).map factorBlockValue).prod) = 33500257881579753966113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_6311
      · exact prime_eightyThreeCC_20219011
      · exact prime_eightyThreeCC_8204272621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33500257881579753966113) ^ 16750128940789876983056 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 33500257881579753966113) ^ 5308232907871930592 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 33500257881579753966113) ^ 1656869264356192 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 33500257881579753966113) ^ 4083269709472 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_37291502591427945023333 : Nat.Prime 37291502591427945023333 := by
  apply lucas_primality 37291502591427945023333 (2 : ZMod 37291502591427945023333)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (113, 1), (10111, 1), (627673777358387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (113, 1), (10111, 1), (627673777358387, 1)] : List FactorBlock).map factorBlockValue).prod) = 37291502591427945023333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_13
      · exact prime_eightyThreeCC_113
      · exact prime_eightyThreeCC_10111
      · exact prime_eightyThreeCC_627673777358387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37291502591427945023333) ^ 18645751295713972511666 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37291502591427945023333) ^ 2868577122417534232564 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37291502591427945023333) ^ 330013297269273849764 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37291502591427945023333) ^ 3688211115757882012 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37291502591427945023333) ^ 59412236 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_63101674113572457624973 : Nat.Prime 63101674113572457624973 := by
  apply lucas_primality 63101674113572457624973 (5 : ZMod 63101674113572457624973)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (317, 1), (991, 1), (6845087, 1), (46139393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (317, 1), (991, 1), (6845087, 1), (46139393, 1)] : List FactorBlock).map factorBlockValue).prod) = 63101674113572457624973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_53
      · exact prime_eightyThreeCC_317
      · exact prime_eightyThreeCC_991
      · exact prime_eightyThreeCC_6845087
      · exact prime_eightyThreeCC_46139393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 63101674113572457624973) ^ 31550837056786228812486 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 63101674113572457624973) ^ 21033891371190819208324 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 63101674113572457624973) ^ 1190597624784385992924 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 63101674113572457624973) ^ 199058908875622894716 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 63101674113572457624973) ^ 63674746835088251892 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 63101674113572457624973) ^ 9218535003802356 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 63101674113572457624973) ^ 1367631215121804 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_80265209313110768896333 : Nat.Prime 80265209313110768896333 := by
  apply lucas_primality 80265209313110768896333 (2 : ZMod 80265209313110768896333)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (14746287463, 1), (23873154013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (14746287463, 1), (23873154013, 1)] : List FactorBlock).map factorBlockValue).prod) = 80265209313110768896333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_14746287463
      · exact prime_eightyThreeCC_23873154013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 80265209313110768896333) ^ 40132604656555384448166 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 80265209313110768896333) ^ 26755069771036922965444 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 80265209313110768896333) ^ 4224484700690040468228 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 80265209313110768896333) ^ 5443079114964 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 80265209313110768896333) ^ 3362153541564 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_140941337798117094832259 : Nat.Prime 140941337798117094832259 := by
  apply lucas_primality 140941337798117094832259 (2 : ZMod 140941337798117094832259)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3287973433, 1), (3061836909359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3287973433, 1), (3061836909359, 1)] : List FactorBlock).map factorBlockValue).prod) = 140941337798117094832259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_3287973433
      · exact prime_eightyThreeCC_3061836909359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 140941337798117094832259) ^ 70470668899058547416129 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 140941337798117094832259) ^ 20134476828302442118894 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 140941337798117094832259) ^ 42865716731026 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 140941337798117094832259) ^ 46031628062 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_204851460333752084780089 : Nat.Prime 204851460333752084780089 := by
  apply lucas_primality 204851460333752084780089 (11 : ZMod 204851460333752084780089)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (23, 1), (37, 1), (421, 1), (641, 1), (859, 1), (6181116559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (23, 1), (37, 1), (421, 1), (641, 1), (859, 1), (6181116559, 1)] : List FactorBlock).map factorBlockValue).prod) = 204851460333752084780089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_23
      · exact prime_eightyThreeCC_37
      · exact prime_eightyThreeCC_421
      · exact prime_eightyThreeCC_641
      · exact prime_eightyThreeCC_859
      · exact prime_eightyThreeCC_6181116559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 204851460333752084780089) ^ 102425730166876042390044 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 204851460333752084780089) ^ 68283820111250694926696 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 204851460333752084780089) ^ 29264494333393154968584 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 204851460333752084780089) ^ 8906585231902264555656 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 204851460333752084780089) ^ 5536525954966272561624 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 204851460333752084780089) ^ 486583041172807802328 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 204851460333752084780089) ^ 319581061363107776568 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 204851460333752084780089) ^ 238476670935683451432 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (11 : ZMod 204851460333752084780089) ^ 33141497717832 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_230789849525227330763723 : Nat.Prime 230789849525227330763723 := by
  apply lucas_primality 230789849525227330763723 (2 : ZMod 230789849525227330763723)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (361739576058350048219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (361739576058350048219, 1)] : List FactorBlock).map factorBlockValue).prod) = 230789849525227330763723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_29
      · exact prime_eightyThreeCC_361739576058350048219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 230789849525227330763723) ^ 115394924762613665381861 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 230789849525227330763723) ^ 20980895411384302796702 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 230789849525227330763723) ^ 7958270673283701060818 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 230789849525227330763723) ^ 638 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_461579699050454661527447 : Nat.Prime 461579699050454661527447 := by
  apply lucas_primality 461579699050454661527447 (5 : ZMod 461579699050454661527447)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (230789849525227330763723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (230789849525227330763723, 1)] : List FactorBlock).map factorBlockValue).prod) = 461579699050454661527447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_230789849525227330763723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 461579699050454661527447) ^ 230789849525227330763723 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 461579699050454661527447) ^ 2 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_651092814691063527389429 : Nat.Prime 651092814691063527389429 := by
  apply lucas_primality 651092814691063527389429 (3 : ZMod 651092814691063527389429)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (32587, 1), (51495205593263863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (32587, 1), (51495205593263863, 1)] : List FactorBlock).map factorBlockValue).prod) = 651092814691063527389429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_97
      · exact prime_eightyThreeCC_32587
      · exact prime_eightyThreeCC_51495205593263863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 651092814691063527389429) ^ 325546407345531763694714 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 651092814691063527389429) ^ 6712297058670758014324 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 651092814691063527389429) ^ 19980139770186378844 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 651092814691063527389429) ^ 12643756 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_800588654487511278481219 : Nat.Prime 800588654487511278481219 := by
  apply lucas_primality 800588654487511278481219 (3 : ZMod 800588654487511278481219)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1549, 1), (12305767999131717521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1549, 1), (12305767999131717521, 1)] : List FactorBlock).map factorBlockValue).prod) = 800588654487511278481219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_1549
      · exact prime_eightyThreeCC_12305767999131717521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 800588654487511278481219) ^ 400294327243755639240609 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 800588654487511278481219) ^ 266862884829170426160406 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 800588654487511278481219) ^ 114369807783930182640174 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 800588654487511278481219) ^ 516842255963532135882 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 800588654487511278481219) ^ 65058 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_3389339298857911626258739 : Nat.Prime 3389339298857911626258739 := by
  apply lucas_primality 3389339298857911626258739 (2 : ZMod 3389339298857911626258739)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (26899518244904060525863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (26899518244904060525863, 1)] : List FactorBlock).map factorBlockValue).prod) = 3389339298857911626258739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_26899518244904060525863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3389339298857911626258739) ^ 1694669649428955813129369 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3389339298857911626258739) ^ 1129779766285970542086246 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3389339298857911626258739) ^ 484191328408273089465534 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3389339298857911626258739) ^ 126 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_5964149479154820239679269 : Nat.Prime 5964149479154820239679269 := by
  apply lucas_primality 5964149479154820239679269 (2 : ZMod 5964149479154820239679269)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18899, 1), (78895040467151968883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18899, 1), (78895040467151968883, 1)] : List FactorBlock).map factorBlockValue).prod) = 5964149479154820239679269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_18899
      · exact prime_eightyThreeCC_78895040467151968883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5964149479154820239679269) ^ 2982074739577410119839634 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5964149479154820239679269) ^ 315580161868607875532 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5964149479154820239679269) ^ 75596 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_18331431231185177919567161 : Nat.Prime 18331431231185177919567161 := by
  apply lucas_primality 18331431231185177919567161 (3 : ZMod 18331431231185177919567161)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (761, 1), (54746837985859449049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (761, 1), (54746837985859449049, 1)] : List FactorBlock).map factorBlockValue).prod) = 18331431231185177919567161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_761
      · exact prime_eightyThreeCC_54746837985859449049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18331431231185177919567161) ^ 9165715615592588959783580 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 18331431231185177919567161) ^ 3666286246237035583913432 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 18331431231185177919567161) ^ 1666493748289561629051560 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 18331431231185177919567161) ^ 24088608713778157581560 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 18331431231185177919567161) ^ 334840 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_33129018021787392776314319 : Nat.Prime 33129018021787392776314319 := by
  apply lucas_primality 33129018021787392776314319 (13 : ZMod 33129018021787392776314319)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (1997, 1), (574540927, 1), (39991926901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (1997, 1), (574540927, 1), (39991926901, 1)] : List FactorBlock).map factorBlockValue).prod) = 33129018021787392776314319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_19
      · exact prime_eightyThreeCC_1997
      · exact prime_eightyThreeCC_574540927
      · exact prime_eightyThreeCC_39991926901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 33129018021787392776314319) ^ 16564509010893696388157159 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 33129018021787392776314319) ^ 1743632527462494356648122 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 33129018021787392776314319) ^ 16589393100544513157894 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 33129018021787392776314319) ^ 57661719931376434 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (13 : ZMod 33129018021787392776314319) ^ 828392642940118 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_44684950537583905921422137 : Nat.Prime 44684950537583905921422137 := by
  apply lucas_primality 44684950537583905921422137 (3 : ZMod 44684950537583905921422137)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2411, 1), (2316722860720857834997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2411, 1), (2316722860720857834997, 1)] : List FactorBlock).map factorBlockValue).prod) = 44684950537583905921422137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_2411
      · exact prime_eightyThreeCC_2316722860720857834997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 44684950537583905921422137) ^ 22342475268791952960711068 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 44684950537583905921422137) ^ 18533782885766862679976 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 44684950537583905921422137) ^ 19288 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_74565464574874055777692259 : Nat.Prime 74565464574874055777692259 := by
  apply lucas_primality 74565464574874055777692259 (2 : ZMod 74565464574874055777692259)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3389339298857911626258739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3389339298857911626258739, 1)] : List FactorBlock).map factorBlockValue).prod) = 74565464574874055777692259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_3389339298857911626258739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 74565464574874055777692259) ^ 37282732287437027888846129 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 74565464574874055777692259) ^ 6778678597715823252517478 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 74565464574874055777692259) ^ 22 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_204008630728761449903207927 : Nat.Prime 204008630728761449903207927 := by
  apply lucas_primality 204008630728761449903207927 (5 : ZMod 204008630728761449903207927)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (307, 1), (7919, 1), (52223, 1), (10169999202983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (307, 1), (7919, 1), (52223, 1), (10169999202983, 1)] : List FactorBlock).map factorBlockValue).prod) = 204008630728761449903207927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_79
      · exact prime_eightyThreeCC_307
      · exact prime_eightyThreeCC_7919
      · exact prime_eightyThreeCC_52223
      · exact prime_eightyThreeCC_10169999202983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 204008630728761449903207927) ^ 102004315364380724951603963 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 204008630728761449903207927) ^ 2582387730743815821559594 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 204008630728761449903207927) ^ 664523227129516123463218 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 204008630728761449903207927) ^ 25761918263513252923754 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 204008630728761449903207927) ^ 3906490066230615818762 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (5 : ZMod 204008630728761449903207927) ^ 20059847268122 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_380341672017574641098616329 : Nat.Prime 380341672017574641098616329 := by
  apply lucas_primality 380341672017574641098616329 (3 : ZMod 380341672017574641098616329)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103, 1), (461579699050454661527447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103, 1), (461579699050454661527447, 1)] : List FactorBlock).map factorBlockValue).prod) = 380341672017574641098616329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_103
      · exact prime_eightyThreeCC_461579699050454661527447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 380341672017574641098616329) ^ 190170836008787320549308164 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 380341672017574641098616329) ^ 3692637592403637292219576 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 380341672017574641098616329) ^ 824 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_424797192123524923824428627 : Nat.Prime 424797192123524923824428627 := by
  apply lucas_primality 424797192123524923824428627 (2 : ZMod 424797192123524923824428627)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (137, 1), (140941337798117094832259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (137, 1), (140941337798117094832259, 1)] : List FactorBlock).map factorBlockValue).prod) = 424797192123524923824428627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_11
      · exact prime_eightyThreeCC_137
      · exact prime_eightyThreeCC_140941337798117094832259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 424797192123524923824428627) ^ 212398596061762461912214313 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 424797192123524923824428627) ^ 38617926556684083984038966 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 424797192123524923824428627) ^ 3100709431558576086309698 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 424797192123524923824428627) ^ 3014 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_436125117246818921793080057 : Nat.Prime 436125117246818921793080057 := by
  apply lucas_primality 436125117246818921793080057 (3 : ZMod 436125117246818921793080057)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41201, 1), (1323163021670647926607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41201, 1), (1323163021670647926607, 1)] : List FactorBlock).map factorBlockValue).prod) = 436125117246818921793080057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_41201
      · exact prime_eightyThreeCC_1323163021670647926607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 436125117246818921793080057) ^ 218062558623409460896540028 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 436125117246818921793080057) ^ 10585304173365183412856 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 436125117246818921793080057) ^ 329608 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1557589704452924720689571633 : Nat.Prime 1557589704452924720689571633 := by
  apply lucas_primality 1557589704452924720689571633 (3 : ZMod 1557589704452924720689571633)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (167, 1), (6287599, 1), (8174329, 1), (11341739411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (167, 1), (6287599, 1), (8174329, 1), (11341739411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1557589704452924720689571633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_167
      · exact prime_eightyThreeCC_6287599
      · exact prime_eightyThreeCC_8174329
      · exact prime_eightyThreeCC_11341739411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1557589704452924720689571633) ^ 778794852226462360344785816 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1557589704452924720689571633) ^ 9326884457801944435266896 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1557589704452924720689571633) ^ 247724084257428745168 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1557589704452924720689571633) ^ 190546490660325113008 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1557589704452924720689571633) ^ 137332524404701712 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_1752288417509540310775768087 : Nat.Prime 1752288417509540310775768087 := by
  apply lucas_primality 1752288417509540310775768087 (3 : ZMod 1752288417509540310775768087)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (167, 1), (6287599, 1), (8174329, 1), (11341739411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (167, 1), (6287599, 1), (8174329, 1), (11341739411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1752288417509540310775768087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_167
      · exact prime_eightyThreeCC_6287599
      · exact prime_eightyThreeCC_8174329
      · exact prime_eightyThreeCC_11341739411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1752288417509540310775768087) ^ 876144208754770155387884043 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1752288417509540310775768087) ^ 584096139169846770258589362 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1752288417509540310775768087) ^ 10492745015027187489675258 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1752288417509540310775768087) ^ 278689594789607338314 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1752288417509540310775768087) ^ 214364801992865752134 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1752288417509540310775768087) ^ 154499089955289426 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_10903127931170473044827001427 : Nat.Prime 10903127931170473044827001427 := by
  apply lucas_primality 10903127931170473044827001427 (2 : ZMod 10903127931170473044827001427)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (173, 1), (22937, 1), (679691, 1), (17617849, 1), (38243069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (173, 1), (22937, 1), (679691, 1), (17617849, 1), (38243069, 1)] : List FactorBlock).map factorBlockValue).prod) = 10903127931170473044827001427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_173
      · exact prime_eightyThreeCC_22937
      · exact prime_eightyThreeCC_679691
      · exact prime_eightyThreeCC_17617849
      · exact prime_eightyThreeCC_38243069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10903127931170473044827001427) ^ 5451563965585236522413500713 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10903127931170473044827001427) ^ 3634375977056824348275667142 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10903127931170473044827001427) ^ 63023860873817763264895962 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10903127931170473044827001427) ^ 475351089121091382692898 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10903127931170473044827001427) ^ 16041301019390389228086 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10903127931170473044827001427) ^ 618868281319159509474 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 10903127931170473044827001427) ^ 285100757242324695354 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_12266018922566782175430376603 : Nat.Prime 12266018922566782175430376603 := by
  apply lucas_primality 12266018922566782175430376603 (2 : ZMod 12266018922566782175430376603)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (167, 1), (6287599, 1), (8174329, 1), (11341739411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (167, 1), (6287599, 1), (8174329, 1), (11341739411, 1)] : List FactorBlock).map factorBlockValue).prod) = 12266018922566782175430376603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_7
      · exact prime_eightyThreeCC_167
      · exact prime_eightyThreeCC_6287599
      · exact prime_eightyThreeCC_8174329
      · exact prime_eightyThreeCC_11341739411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12266018922566782175430376603) ^ 6133009461283391087715188301 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12266018922566782175430376603) ^ 4088672974188927391810125534 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12266018922566782175430376603) ^ 1752288417509540310775768086 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12266018922566782175430376603) ^ 73449215105190312427726806 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12266018922566782175430376603) ^ 1950827163527251368198 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12266018922566782175430376603) ^ 1500553613950060264938 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 12266018922566782175430376603) ^ 1081493629687025982 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_19625630276106851480688602579 : Nat.Prime 19625630276106851480688602579 := by
  apply lucas_primality 19625630276106851480688602579 (2 : ZMod 19625630276106851480688602579)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (552731, 1), (9032753, 1), (1965439409489723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (552731, 1), (9032753, 1), (1965439409489723, 1)] : List FactorBlock).map factorBlockValue).prod) = 19625630276106851480688602579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_552731
      · exact prime_eightyThreeCC_9032753
      · exact prime_eightyThreeCC_1965439409489723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19625630276106851480688602579) ^ 9812815138053425740344301289 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 19625630276106851480688602579) ^ 35506657444773047794838 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 19625630276106851480688602579) ^ 2172718580493328167026 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 19625630276106851480688602579) ^ 9985365196886 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_49064075690267128701721506433 : Nat.Prime 49064075690267128701721506433 := by
  apply lucas_primality 49064075690267128701721506433 (15 : ZMod 49064075690267128701721506433)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (17, 1), (41, 1), (181, 1), (2237, 1), (452746456823018447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (17, 1), (41, 1), (181, 1), (2237, 1), (452746456823018447, 1)] : List FactorBlock).map factorBlockValue).prod) = 49064075690267128701721506433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_3
      · exact prime_eightyThreeCC_17
      · exact prime_eightyThreeCC_41
      · exact prime_eightyThreeCC_181
      · exact prime_eightyThreeCC_2237
      · exact prime_eightyThreeCC_452746456823018447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 49064075690267128701721506433) ^ 24532037845133564350860753216 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (15 : ZMod 49064075690267128701721506433) ^ 16354691896755709567240502144 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (15 : ZMod 49064075690267128701721506433) ^ 2886122099427478158924794496 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (15 : ZMod 49064075690267128701721506433) ^ 1196684772933344602481012352 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (15 : ZMod 49064075690267128701721506433) ^ 271072241382691318794041472 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (15 : ZMod 49064075690267128701721506433) ^ 21932979745313870675780736 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (15 : ZMod 49064075690267128701721506433) ^ 108369872256 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem prime_eightyThreeCC_98128151380534257403443012821 : Nat.Prime 98128151380534257403443012821 := by
  apply lucas_primality 98128151380534257403443012821 (2 : ZMod 98128151380534257403443012821)
  · rw [← eightyThreeCCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (577, 1), (10650752509, 1), (798376077652037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (577, 1), (10650752509, 1), (798376077652037, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_eightyThreeCC_2
      · exact prime_eightyThreeCC_5
      · exact prime_eightyThreeCC_577
      · exact prime_eightyThreeCC_10650752509
      · exact prime_eightyThreeCC_798376077652037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 98128151380534257403443012821) ^ 49064075690267128701721506410 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 98128151380534257403443012821) ^ 19625630276106851480688602564 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 98128151380534257403443012821) ^ 170066120243560238134216660 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 98128151380534257403443012821) ^ 9213259936104506980 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide
    · change (2 : ZMod 98128151380534257403443012821) ^ 122909683953860 ≠ 1
      rw [← eightyThreeCCFastPow_eq_pow]
      decide

private theorem phi_eightyThreeCC_98128151380534257403443012800 : Nat.totient 98128151380534257403443012800 = 37542396223167833345637273600 := by
  rw [← show ((([(2, 6), (5, 2), (23, 1), (16411, 1), (5836793117, 1), (27837898883, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_5, prime_eightyThreeCC_23, prime_eightyThreeCC_16411, prime_eightyThreeCC_5836793117, prime_eightyThreeCC_27837898883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012801 : Nat.totient 98128151380534257403443012801 = 64587483230832387684956697600 := by
  rw [← show ((([(3, 1), (79, 1), (20627, 1), (974513, 1), (81504923, 1), (252718901, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_79, prime_eightyThreeCC_20627, prime_eightyThreeCC_974513, prime_eightyThreeCC_81504923, prime_eightyThreeCC_252718901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012802 : Nat.totient 98128151380534257403443012802 = 41548213248680625458876658000 := by
  rw [← show ((([(2, 1), (7, 1), (83, 1), (1809271, 1), (46674950617554267451, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_7, prime_eightyThreeCC_83, prime_eightyThreeCC_1809271, prime_eightyThreeCC_46674950617554267451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012803 : Nat.totient 98128151380534257403443012803 = 98128151380377156204207999000 := by
  rw [← show ((([(624619939303, 1), (157100574615074501, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_624619939303, prime_eightyThreeCC_157100574615074501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012804 : Nat.totient 98128151380534257403443012804 = 28162283653250562176655814080 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (19, 2), (3323, 1), (619700922902133969899, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_11, prime_eightyThreeCC_19, prime_eightyThreeCC_3323, prime_eightyThreeCC_619700922902133969899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012805 : Nat.totient 98128151380534257403443012805 = 77690828480682900531677437440 := by
  rw [← show ((([(5, 1), (97, 1), (32531, 1), (6219485577470387953723, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_5, prime_eightyThreeCC_97, prime_eightyThreeCC_32531, prime_eightyThreeCC_6219485577470387953723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012806 : Nat.totient 98128151380534257403443012806 = 48984554264528304384420870720 := by
  rw [← show ((([(2, 1), (617, 1), (51452503, 1), (706741331, 1), (2186812063, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_617, prime_eightyThreeCC_51452503, prime_eightyThreeCC_706741331, prime_eightyThreeCC_2186812063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012807 : Nat.totient 98128151380534257403443012807 = 65332018301302057883786003520 := by
  rw [← show ((([(3, 3), (761, 1), (83219, 1), (57388213270765035199, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_761, prime_eightyThreeCC_83219, prime_eightyThreeCC_57388213270765035199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012808 : Nat.totient 98128151380534257403443012808 = 48988242483827458913565021760 := by
  rw [← show ((([(2, 3), (647, 1), (3570831773, 1), (5309210678451371, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_647, prime_eightyThreeCC_3570831773, prime_eightyThreeCC_5309210678451371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012809 : Nat.totient 98128151380534257403443012809 = 76739934155098480976285936640 := by
  rw [← show ((([(7, 3), (13, 1), (163, 1), (241, 1), (743, 1), (753984962256915679, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_7, prime_eightyThreeCC_13, prime_eightyThreeCC_163, prime_eightyThreeCC_241, prime_eightyThreeCC_743, prime_eightyThreeCC_753984962256915679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012810 : Nat.totient 98128151380534257403443012810 = 25423118681974672226744709120 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (59, 1), (113, 1), (383, 1), (3821, 1), (335247922940194267, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_5, prime_eightyThreeCC_59, prime_eightyThreeCC_113, prime_eightyThreeCC_383, prime_eightyThreeCC_3821, prime_eightyThreeCC_335247922940194267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012811 : Nat.totient 98128151380534257403443012811 = 98103626869040154713429065728 := by
  rw [← show ((([(4373, 1), (47057, 1), (730174639, 1), (653075150209, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_4373, prime_eightyThreeCC_47057, prime_eightyThreeCC_730174639, prime_eightyThreeCC_653075150209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012812 : Nat.totient 98128151380534257403443012812 = 48784171302024657385163558400 := by
  rw [← show ((([(2, 2), (227, 1), (857, 1), (7213, 1), (3644277379, 1), (4797329951, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_227, prime_eightyThreeCC_857, prime_eightyThreeCC_7213, prime_eightyThreeCC_3644277379, prime_eightyThreeCC_4797329951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012813 : Nat.totient 98128151380534257403443012813 = 59822724417057474737247129600 := by
  rw [← show ((([(3, 1), (17, 1), (37, 1), (1021, 1), (2381, 1), (21391270505312129099, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_17, prime_eightyThreeCC_37, prime_eightyThreeCC_1021, prime_eightyThreeCC_2381, prime_eightyThreeCC_21391270505312129099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012814 : Nat.totient 98128151380534257403443012814 = 49064075623819315819410636960 := by
  rw [← show ((([(2, 1), (738385111, 1), (66447812881572484337, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_738385111, prime_eightyThreeCC_66447812881572484337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012815 : Nat.totient 98128151380534257403443012815 = 71365900600231771936985769600 := by
  rw [← show ((([(5, 1), (11, 1), (2578573, 1), (691913010381635377421, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_5, prime_eightyThreeCC_11, prime_eightyThreeCC_2578573, prime_eightyThreeCC_691913010381635377421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012816 : Nat.totient 98128151380534257403443012816 = 27868722915823965840930232320 := by
  rw [← show ((([(2, 4), (3, 2), (7, 1), (167, 1), (6287599, 1), (8174329, 1), (11341739411, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_7, prime_eightyThreeCC_167, prime_eightyThreeCC_6287599, prime_eightyThreeCC_8174329, prime_eightyThreeCC_11341739411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012817 : Nat.totient 98128151380534257403443012817 = 94931268358802368589069783040 := by
  rw [← show ((([(67, 1), (71, 1), (257, 1), (80265209313110768896333, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_67, prime_eightyThreeCC_71, prime_eightyThreeCC_257, prime_eightyThreeCC_80265209313110768896333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012818 : Nat.totient 98128151380534257403443012818 = 49064012645104357265077596576 := by
  rw [← show ((([(2, 1), (823913, 1), (14037967, 1), (4242072133669679, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_823913, prime_eightyThreeCC_14037967, prime_eightyThreeCC_4242072133669679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012819 : Nat.totient 98128151380534257403443012819 = 61026252506224232133575370240 := by
  rw [← show ((([(3, 1), (29, 1), (31, 1), (727, 1), (6287, 1), (11317, 1), (703401813659719, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_29, prime_eightyThreeCC_31, prime_eightyThreeCC_727, prime_eightyThreeCC_6287, prime_eightyThreeCC_11317, prime_eightyThreeCC_703401813659719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012820 : Nat.totient 98128151380534257403443012820 = 39183234100437312821635375104 := by
  rw [← show ((([(2, 2), (5, 1), (577, 1), (10650752509, 1), (798376077652037, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_5, prime_eightyThreeCC_577, prime_eightyThreeCC_10650752509, prime_eightyThreeCC_798376077652037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012821 : Nat.totient 98128151380534257403443012821 = 98128151380534257403443012820 := by
  rw [← show ((([(98128151380534257403443012821, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_98128151380534257403443012821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012822 : Nat.totient 98128151380534257403443012822 = 30096180789073683728789667840 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (311, 1), (4781057, 1), (5215403, 1), (162228380129, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_13, prime_eightyThreeCC_311, prime_eightyThreeCC_4781057, prime_eightyThreeCC_5215403, prime_eightyThreeCC_162228380129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012823 : Nat.totient 98128151380534257403443012823 = 74359510398181142237168271360 := by
  rw [← show ((([(7, 1), (19, 1), (23, 1), (41, 1), (2737169, 1), (14026049, 1), (20379490357, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_7, prime_eightyThreeCC_19, prime_eightyThreeCC_23, prime_eightyThreeCC_41, prime_eightyThreeCC_2737169, prime_eightyThreeCC_14026049, prime_eightyThreeCC_20379490357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012824 : Nat.totient 98128151380534257403443012824 = 49064075690267128701721506408 := by
  rw [← show ((([(2, 3), (12266018922566782175430376603, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_12266018922566782175430376603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012825 : Nat.totient 98128151380534257403443012825 = 52335014069618270615169606720 := by
  rw [← show ((([(3, 2), (5, 2), (436125117246818921793080057, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_5, prime_eightyThreeCC_436125117246818921793080057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012826 : Nat.totient 98128151380534257403443012826 = 44565766820432164806456288240 := by
  rw [← show ((([(2, 1), (11, 1), (1223, 1), (30367, 1), (120099884573592689663, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_11, prime_eightyThreeCC_1223, prime_eightyThreeCC_30367, prime_eightyThreeCC_120099884573592689663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012827 : Nat.totient 98128151380534257403443012827 = 97884491829333462630336960000 := by
  rw [← show ((([(521, 1), (1801, 1), (104917, 1), (996773118834235711, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_521, prime_eightyThreeCC_1801, prime_eightyThreeCC_104917, prime_eightyThreeCC_996773118834235711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012828 : Nat.totient 98128151380534257403443012828 = 32332767186152838489055580160 := by
  rw [← show ((([(2, 2), (3, 1), (109, 1), (439, 1), (11953, 1), (2158034941, 1), (6625001203, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_109, prime_eightyThreeCC_439, prime_eightyThreeCC_11953, prime_eightyThreeCC_2158034941, prime_eightyThreeCC_6625001203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012829 : Nat.totient 98128151380534257403443012829 = 98076309002781756709829166400 := by
  rw [← show ((([(1901, 1), (439787, 1), (697782359, 1), (168208960613, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_1901, prime_eightyThreeCC_439787, prime_eightyThreeCC_697782359, prime_eightyThreeCC_168208960613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012830 : Nat.totient 98128151380534257403443012830 = 31357456418966841755552346624 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (17, 1), (103, 1), (800588654487511278481219, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_5, prime_eightyThreeCC_7, prime_eightyThreeCC_17, prime_eightyThreeCC_103, prime_eightyThreeCC_800588654487511278481219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012831 : Nat.totient 98128151380534257403443012831 = 65418767580794780337499402392 := by
  rw [← show ((([(3, 1), (10503879143, 1), (3114028955227423939, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_10503879143, prime_eightyThreeCC_3114028955227423939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012832 : Nat.totient 98128151380534257403443012832 = 49064075690185810690592566272 := by
  rw [← show ((([(2, 5), (603432143687, 1), (5081772263415073, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_603432143687, prime_eightyThreeCC_5081772263415073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012833 : Nat.totient 98128151380534257403443012833 = 95323442402162925181749232000 := by
  rw [← show ((([(53, 1), (101, 1), (18331431231185177919567161, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_53, prime_eightyThreeCC_101, prime_eightyThreeCC_18331431231185177919567161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012834 : Nat.totient 98128151380534257403443012834 = 32518843860951039982169640960 := by
  rw [← show ((([(2, 1), (3, 3), (173, 1), (22937, 1), (679691, 1), (17617849, 1), (38243069, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_173, prime_eightyThreeCC_22937, prime_eightyThreeCC_679691, prime_eightyThreeCC_17617849, prime_eightyThreeCC_38243069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012835 : Nat.totient 98128151380534257403443012835 = 72463865518455443598907680768 := by
  rw [← show ((([(5, 1), (13, 1), (622538467, 1), (2425012987017290177, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_5, prime_eightyThreeCC_13, prime_eightyThreeCC_622538467, prime_eightyThreeCC_2425012987017290177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012836 : Nat.totient 98128151380534257403443012836 = 48886652757340797339530419200 := by
  rw [← show ((([(2, 2), (277, 1), (165211, 1), (122297377, 1), (4383265270511, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_277, prime_eightyThreeCC_165211, prime_eightyThreeCC_122297377, prime_eightyThreeCC_4383265270511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012837 : Nat.totient 98128151380534257403443012837 = 50975663054822990858931435120 := by
  rw [← show ((([(3, 1), (7, 1), (11, 1), (424797192123524923824428627, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_7, prime_eightyThreeCC_11, prime_eightyThreeCC_424797192123524923824428627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012838 : Nat.totient 98128151380534257403443012838 = 49064075346309409018270007136 := by
  rw [← show ((([(2, 1), (146516317, 1), (5975280979, 1), (56042731733, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_146516317, prime_eightyThreeCC_5975280979, prime_eightyThreeCC_56042731733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012839 : Nat.totient 98128151380534257403443012839 = 95845232476771872090868158840 := by
  rw [← show ((([(43, 1), (110311, 1), (20687420403272999488643, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_43, prime_eightyThreeCC_110311, prime_eightyThreeCC_20687420403272999488643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012840 : Nat.totient 98128151380534257403443012840 = 26165487781237500988940389632 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (12959, 1), (63101674113572457624973, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_5, prime_eightyThreeCC_12959, prime_eightyThreeCC_63101674113572457624973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012841 : Nat.totient 98128151380534257403443012841 = 98128089479855324827813734960 := by
  rw [← show ((([(1633679, 1), (53477819, 1), (1123189937032741, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_1633679, prime_eightyThreeCC_53477819, prime_eightyThreeCC_1123189937032741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012842 : Nat.totient 98128151380534257403443012842 = 46481636543638541865127891920 := by
  rw [← show ((([(2, 1), (19, 1), (389381, 1), (6631858701816355040939, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_19, prime_eightyThreeCC_389381, prime_eightyThreeCC_6631858701816355040939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012843 : Nat.totient 98128151380534257403443012843 = 65418767587022838268962008556 := by
  rw [← show ((([(3, 2), (10903127931170473044827001427, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_10903127931170473044827001427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012844 : Nat.totient 98128151380534257403443012844 = 41160136445330478789286126416 := by
  rw [← show ((([(2, 2), (7, 1), (47, 1), (74565464574874055777692259, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_7, prime_eightyThreeCC_47, prime_eightyThreeCC_74565464574874055777692259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012845 : Nat.totient 98128151380534257403443012845 = 78410557158360982730033841024 := by
  rw [← show ((([(5, 1), (907, 1), (14489, 1), (1493406074479103486003, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_5, prime_eightyThreeCC_907, prime_eightyThreeCC_14489, prime_eightyThreeCC_1493406074479103486003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012846 : Nat.totient 98128151380534257403443012846 = 31287236672027790541816765344 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (1178048273989, 1), (603603075042703, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_23, prime_eightyThreeCC_1178048273989, prime_eightyThreeCC_603603075042703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012847 : Nat.totient 98128151380534257403443012847 = 92088235398312693849505996800 := by
  rw [← show ((([(17, 1), (349, 1), (32237, 1), (858397, 1), (1187941, 1), (503131591, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_17, prime_eightyThreeCC_349, prime_eightyThreeCC_32237, prime_eightyThreeCC_858397, prime_eightyThreeCC_1187941, prime_eightyThreeCC_503131591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012848 : Nat.totient 98128151380534257403443012848 = 39752904061446451616012912640 := by
  rw [← show ((([(2, 4), (11, 2), (13, 3), (29, 1), (140129443, 1), (5677155812077, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_11, prime_eightyThreeCC_13, prime_eightyThreeCC_29, prime_eightyThreeCC_140129443, prime_eightyThreeCC_5677155812077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012849 : Nat.totient 98128151380534257403443012849 = 65418767117447769526552196880 := by
  rw [← show ((([(3, 1), (139314823, 1), (234787534371065591021, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_139314823, prime_eightyThreeCC_234787534371065591021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012850 : Nat.totient 98128151380534257403443012850 = 36816283844009627511945600000 := by
  rw [← show ((([(2, 1), (5, 2), (31, 1), (37, 1), (397, 1), (751, 1), (203417407, 1), (28212504239, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_5, prime_eightyThreeCC_31, prime_eightyThreeCC_37, prime_eightyThreeCC_397, prime_eightyThreeCC_751, prime_eightyThreeCC_203417407, prime_eightyThreeCC_28212504239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012851 : Nat.totient 98128151380534257403443012851 = 84107260691811742556157412608 := by
  rw [← show ((([(7, 1), (32579, 1), (51630919, 1), (8333894000575393, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_7, prime_eightyThreeCC_32579, prime_eightyThreeCC_51630919, prime_eightyThreeCC_8333894000575393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012852 : Nat.totient 98128151380534257403443012852 = 32173164387060412263423937920 := by
  rw [← show ((([(2, 2), (3, 2), (61, 1), (44684950537583905921422137, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_61, prime_eightyThreeCC_44684950537583905921422137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012853 : Nat.totient 98128151380534257403443012853 = 98081917813094201896825646080 := by
  rw [← show ((([(4013, 1), (4523, 1), (1077371, 1), (5018022318062657, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_4013, prime_eightyThreeCC_4523, prime_eightyThreeCC_1077371, prime_eightyThreeCC_5018022318062657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012854 : Nat.totient 98128151380534257403443012854 = 48605096403748798885472783112 := by
  rw [← show ((([(2, 1), (107, 1), (111347, 1), (4118142055560010194763, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_107, prime_eightyThreeCC_111347, prime_eightyThreeCC_4118142055560010194763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012855 : Nat.totient 98128151380534257403443012855 = 51953627648910883211269051392 := by
  rw [← show ((([(3, 1), (5, 1), (139, 1), (10657, 1), (4416239239316667483659, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_5, prime_eightyThreeCC_139, prime_eightyThreeCC_10657, prime_eightyThreeCC_4416239239316667483659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012856 : Nat.totient 98128151380534257403443012856 = 49064075690109844800276136320 := by
  rw [← show ((([(2, 3), (311948422481, 1), (39320663412920047, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_311948422481, prime_eightyThreeCC_39320663412920047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012857 : Nat.totient 98128151380534257403443012857 = 98122187231055102583203317136 := by
  rw [← show ((([(16453, 1), (5964149479154820239679269, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_16453, prime_eightyThreeCC_5964149479154820239679269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012858 : Nat.totient 98128151380534257403443012858 = 27756291078248540730746892768 := by
  rw [← show ((([(2, 1), (3, 1), (7, 2), (127, 1), (467, 1), (5627631934154505774923, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_7, prime_eightyThreeCC_127, prime_eightyThreeCC_467, prime_eightyThreeCC_5627631934154505774923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012859 : Nat.totient 98128151380534257403443012859 = 87896373083243791159520044800 := by
  rw [← show ((([(11, 1), (73, 1), (997, 1), (114479, 1), (1070673581210967931, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_11, prime_eightyThreeCC_73, prime_eightyThreeCC_997, prime_eightyThreeCC_114479, prime_eightyThreeCC_1070673581210967931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012860 : Nat.totient 98128151380534257403443012860 = 39251260033035010763974570880 := by
  rw [← show ((([(2, 2), (5, 1), (75602603, 1), (64897336524599726681, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_5, prime_eightyThreeCC_75602603, prime_eightyThreeCC_64897336524599726681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012861 : Nat.totient 98128151380534257403443012861 = 57208168938073656929698945728 := by
  rw [← show ((([(3, 5), (13, 1), (19, 1), (391739, 1), (4173434291030671019, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_13, prime_eightyThreeCC_19, prime_eightyThreeCC_391739, prime_eightyThreeCC_4173434291030671019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012862 : Nat.totient 98128151380534257403443012862 = 49002307308791082556069647360 := by
  rw [← show ((([(2, 1), (881, 1), (8923, 1), (83813, 1), (74467270253365049, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_881, prime_eightyThreeCC_8923, prime_eightyThreeCC_83813, prime_eightyThreeCC_74467270253365049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012863 : Nat.totient 98128151380534257403443012863 = 98088564243191307970236517080 := by
  rw [← show ((([(3299, 1), (9967, 1), (2984329991929847958811, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3299, prime_eightyThreeCC_9967, prime_eightyThreeCC_2984329991929847958811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012864 : Nat.totient 98128151380534257403443012864 = 29855153183478327565693747200 := by
  rw [← show ((([(2, 8), (3, 1), (17, 1), (41, 1), (181, 1), (2237, 1), (452746456823018447, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_17, prime_eightyThreeCC_41, prime_eightyThreeCC_181, prime_eightyThreeCC_2237, prime_eightyThreeCC_452746456823018447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012865 : Nat.totient 98128151380534257403443012865 = 67267101214394777993480773632 := by
  rw [← show ((([(5, 1), (7, 1), (3517, 1), (40993, 1), (78491173, 1), (247755145403, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_5, prime_eightyThreeCC_7, prime_eightyThreeCC_3517, prime_eightyThreeCC_40993, prime_eightyThreeCC_78491173, prime_eightyThreeCC_247755145403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012866 : Nat.totient 98128151380534257403443012866 = 49064075690267128701721506432 := by
  rw [← show ((([(2, 1), (49064075690267128701721506433, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_49064075690267128701721506433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012867 : Nat.totient 98128151380534257403443012867 = 65367538971148906180963464960 := by
  rw [← show ((([(3, 1), (1277, 1), (477312697, 1), (53663436198976381, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_1277, prime_eightyThreeCC_477312697, prime_eightyThreeCC_53663436198976381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012868 : Nat.totient 98128151380534257403443012868 = 48917180297015871837607802880 := by
  rw [← show ((([(2, 2), (613, 1), (733, 1), (1667881, 1), (32734379685137833, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_613, prime_eightyThreeCC_733, prime_eightyThreeCC_1667881, prime_eightyThreeCC_32734379685137833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012869 : Nat.totient 98128151380534257403443012869 = 92009443111825416383146085376 := by
  rw [← show ((([(23, 1), (59, 1), (353, 1), (204851460333752084780089, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_23, prime_eightyThreeCC_59, prime_eightyThreeCC_353, prime_eightyThreeCC_204851460333752084780089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012870 : Nat.totient 98128151380534257403443012870 = 23786436224944766349531878400 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (11, 1), (10781, 1), (9193891552622435973073, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_5, prime_eightyThreeCC_11, prime_eightyThreeCC_10781, prime_eightyThreeCC_9193891552622435973073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012871 : Nat.totient 98128151380534257403443012871 = 98128151380471968091222535952 := by
  rw [← show ((([(1575400815487, 1), (62287736819661433, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_1575400815487, prime_eightyThreeCC_62287736819661433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012872 : Nat.totient 98128151380534257403443012872 = 42054922020228967458618434064 := by
  rw [← show ((([(2, 3), (7, 1), (1752288417509540310775768087, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_7, prime_eightyThreeCC_1752288417509540310775768087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012873 : Nat.totient 98128151380534257403443012873 = 65093063603389306597126472640 := by
  rw [← show ((([(3, 1), (211, 1), (4157, 1), (37291502591427945023333, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_211, prime_eightyThreeCC_4157, prime_eightyThreeCC_37291502591427945023333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012874 : Nat.totient 98128151380534257403443012874 = 45165950264359807763067297792 := by
  rw [← show ((([(2, 1), (13, 1), (523, 1), (1409, 1), (8543, 1), (599511034433268149, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_13, prime_eightyThreeCC_523, prime_eightyThreeCC_1409, prime_eightyThreeCC_8543, prime_eightyThreeCC_599511034433268149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012875 : Nat.totient 98128151380534257403443012875 = 78445167130502526079369036800 := by
  rw [← show ((([(5, 3), (1459, 1), (22109, 1), (24336561261458751713, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_5, prime_eightyThreeCC_1459, prime_eightyThreeCC_22109, prime_eightyThreeCC_24336561261458751713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012876 : Nat.totient 98128151380534257403443012876 = 32539905119513813369661619200 := by
  rw [← show ((([(2, 2), (3, 1), (193, 1), (21804494731, 1), (1943162116298531, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_193, prime_eightyThreeCC_21804494731, prime_eightyThreeCC_1943162116298531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012877 : Nat.totient 98128151380534257403443012877 = 94726191423773450472833100864 := by
  rw [← show ((([(29, 1), (5197, 1), (651092814691063527389429, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_29, prime_eightyThreeCC_5197, prime_eightyThreeCC_651092814691063527389429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012878 : Nat.totient 98128151380534257403443012878 = 49030946672245341308945190640 := by
  rw [← show ((([(2, 1), (1481, 1), (33129018021787392776314319, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_1481, prime_eightyThreeCC_33129018021787392776314319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012879 : Nat.totient 98128151380534257403443012879 = 56073229360305289944824578752 := by
  rw [← show ((([(3, 2), (7, 1), (1557589704452924720689571633, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_7, prime_eightyThreeCC_1557589704452924720689571633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012880 : Nat.totient 98128151380534257403443012880 = 36373673367355346690013425664 := by
  rw [← show ((([(2, 4), (5, 1), (19, 1), (79, 1), (137, 1), (499, 1), (11953685497077283747, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_5, prime_eightyThreeCC_19, prime_eightyThreeCC_79, prime_eightyThreeCC_137, prime_eightyThreeCC_499, prime_eightyThreeCC_11953685497077283747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012881 : Nat.totient 98128151380534257403443012881 = 81238094567857725632620492800 := by
  rw [← show ((([(11, 1), (17, 1), (31, 1), (6047, 1), (9254916857, 1), (302466880187, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_11, prime_eightyThreeCC_17, prime_eightyThreeCC_31, prime_eightyThreeCC_6047, prime_eightyThreeCC_9254916857, prime_eightyThreeCC_302466880187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012882 : Nat.totient 98128151380534257403443012882 = 31948700449476269852283771552 := by
  rw [← show ((([(2, 1), (3, 1), (43, 1), (380341672017574641098616329, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_43, prime_eightyThreeCC_380341672017574641098616329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012883 : Nat.totient 98128151380534257403443012883 = 98127689295251462476643794944 := by
  rw [← show ((([(221713, 1), (5345953, 1), (95690083, 1), (865187809, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_221713, prime_eightyThreeCC_5345953, prime_eightyThreeCC_95690083, prime_eightyThreeCC_865187809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012884 : Nat.totient 98128151380534257403443012884 = 47944297535063991860928729600 := by
  rw [← show ((([(2, 2), (67, 1), (131, 1), (2591, 1), (2752403, 1), (16518037, 1), (23727373, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_67, prime_eightyThreeCC_131, prime_eightyThreeCC_2591, prime_eightyThreeCC_2752403, prime_eightyThreeCC_16518037, prime_eightyThreeCC_23727373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012885 : Nat.totient 98128151380534257403443012885 = 50797893069827724820512454656 := by
  rw [← show ((([(3, 1), (5, 1), (83, 1), (89, 1), (157, 1), (25291823, 1), (223025475004187, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_5, prime_eightyThreeCC_83, prime_eightyThreeCC_89, prime_eightyThreeCC_157, prime_eightyThreeCC_25291823, prime_eightyThreeCC_223025475004187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012886 : Nat.totient 98128151380534257403443012886 = 41200291260514155699668044800 := by
  rw [← show ((([(2, 1), (7, 1), (53, 1), (829, 1), (4391, 1), (20771, 1), (1749098787216457, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_7, prime_eightyThreeCC_53, prime_eightyThreeCC_829, prime_eightyThreeCC_4391, prime_eightyThreeCC_20771, prime_eightyThreeCC_1749098787216457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012887 : Nat.totient 98128151380534257403443012887 = 88131728474824946358185824032 := by
  rw [← show ((([(13, 1), (37, 1), (204008630728761449903207927, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_13, prime_eightyThreeCC_37, prime_eightyThreeCC_204008630728761449903207927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012888 : Nat.totient 98128151380534257403443012888 = 32079846947400772397948851200 := by
  rw [← show ((([(2, 3), (3, 3), (71, 1), (191, 1), (33500257881579753966113, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_71, prime_eightyThreeCC_191, prime_eightyThreeCC_33500257881579753966113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012889 : Nat.totient 98128151380534257403443012889 = 98128151379400201645436945424 := by
  rw [← show ((([(86528513413, 1), (1134055671477554053, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_86528513413, prime_eightyThreeCC_1134055671477554053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012890 : Nat.totient 98128151380534257403443012890 = 39251185193469494215571188480 := by
  rw [← show ((([(2, 1), (5, 1), (552731, 1), (9032753, 1), (1965439409489723, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_5, prime_eightyThreeCC_552731, prime_eightyThreeCC_9032753, prime_eightyThreeCC_1965439409489723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012891 : Nat.totient 98128151380534257403443012891 = 64020676430427951615291187200 := by
  rw [← show ((([(3, 1), (47, 1), (14797, 1), (34913, 1), (1535531, 1), (877314028361, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_47, prime_eightyThreeCC_14797, prime_eightyThreeCC_34913, prime_eightyThreeCC_1535531, prime_eightyThreeCC_877314028361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012892 : Nat.totient 98128151380534257403443012892 = 42571866108102822661292812800 := by
  rw [← show ((([(2, 2), (11, 1), (23, 1), (461, 1), (74191205017, 1), (2835043679543, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_11, prime_eightyThreeCC_23, prime_eightyThreeCC_461, prime_eightyThreeCC_74191205017, prime_eightyThreeCC_2835043679543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012893 : Nat.totient 98128151380534257403443012893 = 83925796240279843035184817280 := by
  rw [← show ((([(7, 1), (457, 1), (59848289381, 1), (512539847780647, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_7, prime_eightyThreeCC_457, prime_eightyThreeCC_59848289381, prime_eightyThreeCC_512539847780647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012894 : Nat.totient 98128151380534257403443012894 = 32709331204193131620487689600 := by
  rw [← show ((([(2, 1), (3, 1), (1096163, 1), (1573021, 1), (17252111, 1), (549781933, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_1096163, prime_eightyThreeCC_1573021, prime_eightyThreeCC_17252111, prime_eightyThreeCC_549781933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012895 : Nat.totient 98128151380534257403443012895 = 78502521104427405922754410312 := by
  rw [← show ((([(5, 1), (19625630276106851480688602579, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_5, prime_eightyThreeCC_19625630276106851480688602579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012896 : Nat.totient 98128151380534257403443012896 = 49064058937696085479080732928 := by
  rw [← show ((([(2, 5), (2928749, 1), (1047035690201412119597, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_2928749, prime_eightyThreeCC_1047035690201412119597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012897 : Nat.totient 98128151380534257403443012897 = 65418746230792578701032420608 := by
  rw [← show ((([(3, 2), (3063217, 1), (3559371709927985201449, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_3, prime_eightyThreeCC_3063217, prime_eightyThreeCC_3559371709927985201449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012898 : Nat.totient 98128151380534257403443012898 = 46148771351678771486157668352 := by
  rw [← show ((([(2, 1), (17, 1), (1657, 1), (50263, 1), (116639, 1), (297098184492353, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_17, prime_eightyThreeCC_1657, prime_eightyThreeCC_50263, prime_eightyThreeCC_116639, prime_eightyThreeCC_297098184492353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012899 : Nat.totient 98128151380534257403443012899 = 92816161074809972523745560000 := by
  rw [← show ((([(19, 1), (631, 1), (3952601, 1), (2070750052023220591, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_19, prime_eightyThreeCC_631, prime_eightyThreeCC_3952601, prime_eightyThreeCC_2070750052023220591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012900 : Nat.totient 98128151380534257403443012900 = 20703951046405951543588723200 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (7, 1), (13, 1), (1959943, 1), (1833950160543826711, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_2, prime_eightyThreeCC_3, prime_eightyThreeCC_5, prime_eightyThreeCC_7, prime_eightyThreeCC_13, prime_eightyThreeCC_1959943, prime_eightyThreeCC_1833950160543826711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_eightyThreeCC_98128151380534257403443012901 : Nat.totient 98128151380534257403443012901 = 98128151203607351138659005792 := by
  rw [← show ((([(554625373, 1), (176926906264229381737, 1)] : List FactorBlock).map factorBlockValue).prod) = 98128151380534257403443012901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_eightyThreeCC_554625373, prime_eightyThreeCC_176926906264229381737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64EightyThreeCC : certifiedKill 1 98128151380534257403443012799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_eightyThreeCC_98128151380534257403443012800, phi_eightyThreeCC_98128151380534257403443012801, phi_eightyThreeCC_98128151380534257403443012802,
    phi_eightyThreeCC_98128151380534257403443012803, phi_eightyThreeCC_98128151380534257403443012804, phi_eightyThreeCC_98128151380534257403443012805,
    phi_eightyThreeCC_98128151380534257403443012806, phi_eightyThreeCC_98128151380534257403443012807, phi_eightyThreeCC_98128151380534257403443012808,
    phi_eightyThreeCC_98128151380534257403443012809, phi_eightyThreeCC_98128151380534257403443012810, phi_eightyThreeCC_98128151380534257403443012811,
    phi_eightyThreeCC_98128151380534257403443012812, phi_eightyThreeCC_98128151380534257403443012813, phi_eightyThreeCC_98128151380534257403443012814,
    phi_eightyThreeCC_98128151380534257403443012815, phi_eightyThreeCC_98128151380534257403443012816, phi_eightyThreeCC_98128151380534257403443012817,
    phi_eightyThreeCC_98128151380534257403443012818, phi_eightyThreeCC_98128151380534257403443012819, phi_eightyThreeCC_98128151380534257403443012820,
    phi_eightyThreeCC_98128151380534257403443012821, phi_eightyThreeCC_98128151380534257403443012822, phi_eightyThreeCC_98128151380534257403443012823,
    phi_eightyThreeCC_98128151380534257403443012824, phi_eightyThreeCC_98128151380534257403443012825, phi_eightyThreeCC_98128151380534257403443012826,
    phi_eightyThreeCC_98128151380534257403443012827, phi_eightyThreeCC_98128151380534257403443012828, phi_eightyThreeCC_98128151380534257403443012829,
    phi_eightyThreeCC_98128151380534257403443012830, phi_eightyThreeCC_98128151380534257403443012831, phi_eightyThreeCC_98128151380534257403443012832,
    phi_eightyThreeCC_98128151380534257403443012833, phi_eightyThreeCC_98128151380534257403443012834, phi_eightyThreeCC_98128151380534257403443012835,
    phi_eightyThreeCC_98128151380534257403443012836, phi_eightyThreeCC_98128151380534257403443012837, phi_eightyThreeCC_98128151380534257403443012838,
    phi_eightyThreeCC_98128151380534257403443012839, phi_eightyThreeCC_98128151380534257403443012840, phi_eightyThreeCC_98128151380534257403443012841,
    phi_eightyThreeCC_98128151380534257403443012842, phi_eightyThreeCC_98128151380534257403443012843, phi_eightyThreeCC_98128151380534257403443012844,
    phi_eightyThreeCC_98128151380534257403443012845, phi_eightyThreeCC_98128151380534257403443012846, phi_eightyThreeCC_98128151380534257403443012847,
    phi_eightyThreeCC_98128151380534257403443012848, phi_eightyThreeCC_98128151380534257403443012849, phi_eightyThreeCC_98128151380534257403443012850,
    phi_eightyThreeCC_98128151380534257403443012851, phi_eightyThreeCC_98128151380534257403443012852, phi_eightyThreeCC_98128151380534257403443012853,
    phi_eightyThreeCC_98128151380534257403443012854, phi_eightyThreeCC_98128151380534257403443012855, phi_eightyThreeCC_98128151380534257403443012856,
    phi_eightyThreeCC_98128151380534257403443012857, phi_eightyThreeCC_98128151380534257403443012858, phi_eightyThreeCC_98128151380534257403443012859,
    phi_eightyThreeCC_98128151380534257403443012860, phi_eightyThreeCC_98128151380534257403443012861, phi_eightyThreeCC_98128151380534257403443012862,
    phi_eightyThreeCC_98128151380534257403443012863, phi_eightyThreeCC_98128151380534257403443012864, phi_eightyThreeCC_98128151380534257403443012865,
    phi_eightyThreeCC_98128151380534257403443012866, phi_eightyThreeCC_98128151380534257403443012867, phi_eightyThreeCC_98128151380534257403443012868,
    phi_eightyThreeCC_98128151380534257403443012869, phi_eightyThreeCC_98128151380534257403443012870, phi_eightyThreeCC_98128151380534257403443012871,
    phi_eightyThreeCC_98128151380534257403443012872, phi_eightyThreeCC_98128151380534257403443012873, phi_eightyThreeCC_98128151380534257403443012874,
    phi_eightyThreeCC_98128151380534257403443012875, phi_eightyThreeCC_98128151380534257403443012876, phi_eightyThreeCC_98128151380534257403443012877,
    phi_eightyThreeCC_98128151380534257403443012878, phi_eightyThreeCC_98128151380534257403443012879, phi_eightyThreeCC_98128151380534257403443012880,
    phi_eightyThreeCC_98128151380534257403443012881, phi_eightyThreeCC_98128151380534257403443012882, phi_eightyThreeCC_98128151380534257403443012883,
    phi_eightyThreeCC_98128151380534257403443012884, phi_eightyThreeCC_98128151380534257403443012885, phi_eightyThreeCC_98128151380534257403443012886,
    phi_eightyThreeCC_98128151380534257403443012887, phi_eightyThreeCC_98128151380534257403443012888, phi_eightyThreeCC_98128151380534257403443012889,
    phi_eightyThreeCC_98128151380534257403443012890, phi_eightyThreeCC_98128151380534257403443012891, phi_eightyThreeCC_98128151380534257403443012892,
    phi_eightyThreeCC_98128151380534257403443012893, phi_eightyThreeCC_98128151380534257403443012894, phi_eightyThreeCC_98128151380534257403443012895,
    phi_eightyThreeCC_98128151380534257403443012896, phi_eightyThreeCC_98128151380534257403443012897, phi_eightyThreeCC_98128151380534257403443012898,
    phi_eightyThreeCC_98128151380534257403443012899, phi_eightyThreeCC_98128151380534257403443012900, phi_eightyThreeCC_98128151380534257403443012901]

end TotientTailPeriodKiller
end Erdos249257
