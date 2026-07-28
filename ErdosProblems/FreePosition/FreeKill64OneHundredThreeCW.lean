import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThreeCWFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThreeCWFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThreeCWFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThreeCWFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThreeCWFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThreeCWFastPow a n * oneHundredThreeCWFastPow a n * a else oneHundredThreeCWFastPow a n * oneHundredThreeCWFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThreeCW_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredThreeCW_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredThreeCW_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredThreeCW_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredThreeCW_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredThreeCW_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredThreeCW_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredThreeCW_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredThreeCW_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredThreeCW_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredThreeCW_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredThreeCW_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredThreeCW_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredThreeCW_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredThreeCW_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredThreeCW_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredThreeCW_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredThreeCW_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredThreeCW_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredThreeCW_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredThreeCW_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredThreeCW_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredThreeCW_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredThreeCW_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredThreeCW_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredThreeCW_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredThreeCW_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredThreeCW_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredThreeCW_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredThreeCW_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredThreeCW_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredThreeCW_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredThreeCW_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredThreeCW_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredThreeCW_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredThreeCW_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredThreeCW_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredThreeCW_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredThreeCW_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredThreeCW_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredThreeCW_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredThreeCW_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredThreeCW_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredThreeCW_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredThreeCW_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredThreeCW_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredThreeCW_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredThreeCW_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredThreeCW_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredThreeCW_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredThreeCW_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredThreeCW_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredThreeCW_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredThreeCW_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredThreeCW_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredThreeCW_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredThreeCW_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredThreeCW_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredThreeCW_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredThreeCW_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredThreeCW_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredThreeCW_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredThreeCW_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredThreeCW_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredThreeCW_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredThreeCW_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredThreeCW_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredThreeCW_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredThreeCW_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredThreeCW_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredThreeCW_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredThreeCW_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredThreeCW_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredThreeCW_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredThreeCW_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredThreeCW_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredThreeCW_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredThreeCW_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredThreeCW_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredThreeCW_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredThreeCW_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredThreeCW_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredThreeCW_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredThreeCW_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredThreeCW_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredThreeCW_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredThreeCW_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredThreeCW_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredThreeCW_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredThreeCW_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredThreeCW_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredThreeCW_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredThreeCW_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredThreeCW_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredThreeCW_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredThreeCW_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredThreeCW_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredThreeCW_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredThreeCW_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredThreeCW_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredThreeCW_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredThreeCW_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredThreeCW_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredThreeCW_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredThreeCW_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredThreeCW_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredThreeCW_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredThreeCW_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredThreeCW_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_oneHundredThreeCW_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredThreeCW_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredThreeCW_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredThreeCW_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredThreeCW_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredThreeCW_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredThreeCW_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredThreeCW_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_oneHundredThreeCW_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredThreeCW_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_oneHundredThreeCW_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredThreeCW_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredThreeCW_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredThreeCW_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredThreeCW_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_oneHundredThreeCW_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredThreeCW_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_oneHundredThreeCW_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_oneHundredThreeCW_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_oneHundredThreeCW_1801 : Nat.Prime 1801 := by norm_num

private theorem prime_oneHundredThreeCW_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_oneHundredThreeCW_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredThreeCW_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_oneHundredThreeCW_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredThreeCW_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_oneHundredThreeCW_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_oneHundredThreeCW_2111 : Nat.Prime 2111 := by norm_num

private theorem prime_oneHundredThreeCW_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_oneHundredThreeCW_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_oneHundredThreeCW_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_oneHundredThreeCW_2243 : Nat.Prime 2243 := by norm_num

private theorem prime_oneHundredThreeCW_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_oneHundredThreeCW_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_oneHundredThreeCW_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_oneHundredThreeCW_2351 : Nat.Prime 2351 := by norm_num

private theorem prime_oneHundredThreeCW_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_oneHundredThreeCW_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_oneHundredThreeCW_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_oneHundredThreeCW_2683 : Nat.Prime 2683 := by norm_num

private theorem prime_oneHundredThreeCW_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_oneHundredThreeCW_2713 : Nat.Prime 2713 := by norm_num

private theorem prime_oneHundredThreeCW_2749 : Nat.Prime 2749 := by norm_num

private theorem prime_oneHundredThreeCW_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_oneHundredThreeCW_2837 : Nat.Prime 2837 := by norm_num

private theorem prime_oneHundredThreeCW_2861 : Nat.Prime 2861 := by norm_num

private theorem prime_oneHundredThreeCW_2897 : Nat.Prime 2897 := by norm_num

private theorem prime_oneHundredThreeCW_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredThreeCW_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_oneHundredThreeCW_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_oneHundredThreeCW_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_oneHundredThreeCW_3307 : Nat.Prime 3307 := by norm_num

private theorem prime_oneHundredThreeCW_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_oneHundredThreeCW_3331 : Nat.Prime 3331 := by norm_num

private theorem prime_oneHundredThreeCW_3347 : Nat.Prime 3347 := by norm_num

private theorem prime_oneHundredThreeCW_3391 : Nat.Prime 3391 := by norm_num

private theorem prime_oneHundredThreeCW_3511 : Nat.Prime 3511 := by norm_num

private theorem prime_oneHundredThreeCW_3559 : Nat.Prime 3559 := by norm_num

private theorem prime_oneHundredThreeCW_3613 : Nat.Prime 3613 := by norm_num

private theorem prime_oneHundredThreeCW_3631 : Nat.Prime 3631 := by norm_num

private theorem prime_oneHundredThreeCW_3697 : Nat.Prime 3697 := by norm_num

private theorem prime_oneHundredThreeCW_3779 : Nat.Prime 3779 := by norm_num

private theorem prime_oneHundredThreeCW_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_oneHundredThreeCW_4007 : Nat.Prime 4007 := by norm_num

private theorem prime_oneHundredThreeCW_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_oneHundredThreeCW_4127 : Nat.Prime 4127 := by norm_num

private theorem prime_oneHundredThreeCW_4153 : Nat.Prime 4153 := by norm_num

private theorem prime_oneHundredThreeCW_4231 : Nat.Prime 4231 := by norm_num

private theorem prime_oneHundredThreeCW_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_oneHundredThreeCW_4691 : Nat.Prime 4691 := by norm_num

private theorem prime_oneHundredThreeCW_4759 : Nat.Prime 4759 := by norm_num

private theorem prime_oneHundredThreeCW_5021 : Nat.Prime 5021 := by norm_num

private theorem prime_oneHundredThreeCW_5087 : Nat.Prime 5087 := by norm_num

private theorem prime_oneHundredThreeCW_5099 : Nat.Prime 5099 := by norm_num

private theorem prime_oneHundredThreeCW_5309 : Nat.Prime 5309 := by norm_num

private theorem prime_oneHundredThreeCW_5563 : Nat.Prime 5563 := by norm_num

private theorem prime_oneHundredThreeCW_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_oneHundredThreeCW_5591 : Nat.Prime 5591 := by norm_num

private theorem prime_oneHundredThreeCW_5683 : Nat.Prime 5683 := by norm_num

private theorem prime_oneHundredThreeCW_5927 : Nat.Prime 5927 := by norm_num

private theorem prime_oneHundredThreeCW_6151 : Nat.Prime 6151 := by norm_num

private theorem prime_oneHundredThreeCW_6173 : Nat.Prime 6173 := by norm_num

private theorem prime_oneHundredThreeCW_6311 : Nat.Prime 6311 := by norm_num

private theorem prime_oneHundredThreeCW_6659 : Nat.Prime 6659 := by norm_num

private theorem prime_oneHundredThreeCW_6737 : Nat.Prime 6737 := by norm_num

private theorem prime_oneHundredThreeCW_6907 : Nat.Prime 6907 := by norm_num

private theorem prime_oneHundredThreeCW_6983 : Nat.Prime 6983 := by norm_num

private theorem prime_oneHundredThreeCW_7247 : Nat.Prime 7247 := by norm_num

private theorem prime_oneHundredThreeCW_7541 : Nat.Prime 7541 := by norm_num

private theorem prime_oneHundredThreeCW_7573 : Nat.Prime 7573 := by norm_num

private theorem prime_oneHundredThreeCW_7621 : Nat.Prime 7621 := by norm_num

private theorem prime_oneHundredThreeCW_7727 : Nat.Prime 7727 := by norm_num

private theorem prime_oneHundredThreeCW_7753 : Nat.Prime 7753 := by norm_num

private theorem prime_oneHundredThreeCW_8089 : Nat.Prime 8089 := by norm_num

private theorem prime_oneHundredThreeCW_8293 : Nat.Prime 8293 := by norm_num

private theorem prime_oneHundredThreeCW_8423 : Nat.Prime 8423 := by norm_num

private theorem prime_oneHundredThreeCW_8429 : Nat.Prime 8429 := by norm_num

private theorem prime_oneHundredThreeCW_8867 : Nat.Prime 8867 := by norm_num

private theorem prime_oneHundredThreeCW_8941 : Nat.Prime 8941 := by norm_num

private theorem prime_oneHundredThreeCW_9157 : Nat.Prime 9157 := by norm_num

private theorem prime_oneHundredThreeCW_9199 : Nat.Prime 9199 := by norm_num

private theorem prime_oneHundredThreeCW_9221 : Nat.Prime 9221 := by norm_num

private theorem prime_oneHundredThreeCW_9629 : Nat.Prime 9629 := by norm_num

private theorem prime_oneHundredThreeCW_10099 : Nat.Prime 10099 := by norm_num

private theorem prime_oneHundredThreeCW_10733 : Nat.Prime 10733 := by norm_num

private theorem prime_oneHundredThreeCW_11321 : Nat.Prime 11321 := by norm_num

private theorem prime_oneHundredThreeCW_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredThreeCW_11953 : Nat.Prime 11953 := by norm_num

private theorem prime_oneHundredThreeCW_12211 : Nat.Prime 12211 := by norm_num

private theorem prime_oneHundredThreeCW_12413 : Nat.Prime 12413 := by norm_num

private theorem prime_oneHundredThreeCW_12853 : Nat.Prime 12853 := by norm_num

private theorem prime_oneHundredThreeCW_13567 : Nat.Prime 13567 := by norm_num

private theorem prime_oneHundredThreeCW_13931 : Nat.Prime 13931 := by norm_num

private theorem prime_oneHundredThreeCW_14221 : Nat.Prime 14221 := by norm_num

private theorem prime_oneHundredThreeCW_14699 : Nat.Prime 14699 := by norm_num

private theorem prime_oneHundredThreeCW_14879 : Nat.Prime 14879 := by norm_num

private theorem prime_oneHundredThreeCW_14983 : Nat.Prime 14983 := by norm_num

private theorem prime_oneHundredThreeCW_15907 : Nat.Prime 15907 := by norm_num

private theorem prime_oneHundredThreeCW_17189 : Nat.Prime 17189 := by norm_num

private theorem prime_oneHundredThreeCW_18149 : Nat.Prime 18149 := by norm_num

private theorem prime_oneHundredThreeCW_18269 : Nat.Prime 18269 := by norm_num

private theorem prime_oneHundredThreeCW_19219 : Nat.Prime 19219 := by norm_num

private theorem prime_oneHundredThreeCW_19421 : Nat.Prime 19421 := by norm_num

private theorem prime_oneHundredThreeCW_20051 : Nat.Prime 20051 := by norm_num

private theorem prime_oneHundredThreeCW_20347 : Nat.Prime 20347 := by norm_num

private theorem prime_oneHundredThreeCW_20509 : Nat.Prime 20509 := by norm_num

private theorem prime_oneHundredThreeCW_21247 : Nat.Prime 21247 := by norm_num

private theorem prime_oneHundredThreeCW_21269 : Nat.Prime 21269 := by norm_num

private theorem prime_oneHundredThreeCW_22469 : Nat.Prime 22469 := by norm_num

private theorem prime_oneHundredThreeCW_22717 : Nat.Prime 22717 := by norm_num

private theorem prime_oneHundredThreeCW_23887 : Nat.Prime 23887 := by norm_num

private theorem prime_oneHundredThreeCW_24733 : Nat.Prime 24733 := by norm_num

private theorem prime_oneHundredThreeCW_24971 : Nat.Prime 24971 := by norm_num

private theorem prime_oneHundredThreeCW_25169 : Nat.Prime 25169 := by norm_num

private theorem prime_oneHundredThreeCW_25391 : Nat.Prime 25391 := by norm_num

private theorem prime_oneHundredThreeCW_25999 : Nat.Prime 25999 := by norm_num

private theorem prime_oneHundredThreeCW_26251 : Nat.Prime 26251 := by norm_num

private theorem prime_oneHundredThreeCW_26437 : Nat.Prime 26437 := by norm_num

private theorem prime_oneHundredThreeCW_26717 : Nat.Prime 26717 := by norm_num

private theorem prime_oneHundredThreeCW_27541 : Nat.Prime 27541 := by norm_num

private theorem prime_oneHundredThreeCW_30391 : Nat.Prime 30391 := by norm_num

private theorem prime_oneHundredThreeCW_30539 : Nat.Prime 30539 := by norm_num

private theorem prime_oneHundredThreeCW_30643 : Nat.Prime 30643 := by norm_num

private theorem prime_oneHundredThreeCW_31063 : Nat.Prime 31063 := by norm_num

private theorem prime_oneHundredThreeCW_31153 : Nat.Prime 31153 := by norm_num

private theorem prime_oneHundredThreeCW_31327 : Nat.Prime 31327 := by norm_num

private theorem prime_oneHundredThreeCW_31391 : Nat.Prime 31391 := by norm_num

private theorem prime_oneHundredThreeCW_32957 : Nat.Prime 32957 := by norm_num

private theorem prime_oneHundredThreeCW_34141 : Nat.Prime 34141 := by norm_num

private theorem prime_oneHundredThreeCW_35507 : Nat.Prime 35507 := by norm_num

private theorem prime_oneHundredThreeCW_38707 : Nat.Prime 38707 := by norm_num

private theorem prime_oneHundredThreeCW_43711 : Nat.Prime 43711 := by norm_num

private theorem prime_oneHundredThreeCW_44507 : Nat.Prime 44507 := by norm_num

private theorem prime_oneHundredThreeCW_45413 : Nat.Prime 45413 := by norm_num

private theorem prime_oneHundredThreeCW_46133 : Nat.Prime 46133 := by norm_num

private theorem prime_oneHundredThreeCW_53129 : Nat.Prime 53129 := by norm_num

private theorem prime_oneHundredThreeCW_53857 : Nat.Prime 53857 := by norm_num

private theorem prime_oneHundredThreeCW_54011 : Nat.Prime 54011 := by norm_num

private theorem prime_oneHundredThreeCW_56003 : Nat.Prime 56003 := by norm_num

private theorem prime_oneHundredThreeCW_58171 : Nat.Prime 58171 := by norm_num

private theorem prime_oneHundredThreeCW_59797 : Nat.Prime 59797 := by norm_num

private theorem prime_oneHundredThreeCW_61979 : Nat.Prime 61979 := by norm_num

private theorem prime_oneHundredThreeCW_62761 : Nat.Prime 62761 := by norm_num

private theorem prime_oneHundredThreeCW_62873 : Nat.Prime 62873 := by norm_num

private theorem prime_oneHundredThreeCW_65063 : Nat.Prime 65063 := by norm_num

private theorem prime_oneHundredThreeCW_65323 : Nat.Prime 65323 := by norm_num

private theorem prime_oneHundredThreeCW_68611 : Nat.Prime 68611 := by norm_num

private theorem prime_oneHundredThreeCW_68993 : Nat.Prime 68993 := by norm_num

private theorem prime_oneHundredThreeCW_70481 : Nat.Prime 70481 := by norm_num

private theorem prime_oneHundredThreeCW_76303 : Nat.Prime 76303 := by norm_num

private theorem prime_oneHundredThreeCW_76541 : Nat.Prime 76541 := by norm_num

private theorem prime_oneHundredThreeCW_81371 : Nat.Prime 81371 := by norm_num

private theorem prime_oneHundredThreeCW_83117 : Nat.Prime 83117 := by norm_num

private theorem prime_oneHundredThreeCW_84913 : Nat.Prime 84913 := by norm_num

private theorem prime_oneHundredThreeCW_85513 : Nat.Prime 85513 := by norm_num

private theorem prime_oneHundredThreeCW_88379 : Nat.Prime 88379 := by norm_num

private theorem prime_oneHundredThreeCW_90073 : Nat.Prime 90073 := by norm_num

private theorem prime_oneHundredThreeCW_94117 : Nat.Prime 94117 := by norm_num

private theorem prime_oneHundredThreeCW_101009 : Nat.Prime 101009 := by norm_num

private theorem prime_oneHundredThreeCW_102547 : Nat.Prime 102547 := by norm_num

private theorem prime_oneHundredThreeCW_102551 : Nat.Prime 102551 := by norm_num

private theorem prime_oneHundredThreeCW_111029 : Nat.Prime 111029 := by norm_num

private theorem prime_oneHundredThreeCW_113759 : Nat.Prime 113759 := by norm_num

private theorem prime_oneHundredThreeCW_115163 : Nat.Prime 115163 := by norm_num

private theorem prime_oneHundredThreeCW_118411 : Nat.Prime 118411 := by norm_num

private theorem prime_oneHundredThreeCW_125621 : Nat.Prime 125621 := by norm_num

private theorem prime_oneHundredThreeCW_132859 : Nat.Prime 132859 := by norm_num

private theorem prime_oneHundredThreeCW_132947 : Nat.Prime 132947 := by norm_num

private theorem prime_oneHundredThreeCW_141991 : Nat.Prime 141991 := by norm_num

private theorem prime_oneHundredThreeCW_149531 : Nat.Prime 149531 := by norm_num

private theorem prime_oneHundredThreeCW_152239 : Nat.Prime 152239 := by norm_num

private theorem prime_oneHundredThreeCW_170369 : Nat.Prime 170369 := by norm_num

private theorem prime_oneHundredThreeCW_176531 : Nat.Prime 176531 := by norm_num

private theorem prime_oneHundredThreeCW_185753 : Nat.Prime 185753 := by norm_num

private theorem prime_oneHundredThreeCW_191353 : Nat.Prime 191353 := by norm_num

private theorem prime_oneHundredThreeCW_204101 : Nat.Prime 204101 := by norm_num

private theorem prime_oneHundredThreeCW_205883 : Nat.Prime 205883 := by norm_num

private theorem prime_oneHundredThreeCW_207121 : Nat.Prime 207121 := by norm_num

private theorem prime_oneHundredThreeCW_207307 : Nat.Prime 207307 := by norm_num

private theorem prime_oneHundredThreeCW_218047 : Nat.Prime 218047 := by norm_num

private theorem prime_oneHundredThreeCW_219409 : Nat.Prime 219409 := by norm_num

private theorem prime_oneHundredThreeCW_229549 : Nat.Prime 229549 := by norm_num

private theorem prime_oneHundredThreeCW_236519 : Nat.Prime 236519 := by norm_num

private theorem prime_oneHundredThreeCW_238009 : Nat.Prime 238009 := by norm_num

private theorem prime_oneHundredThreeCW_245789 : Nat.Prime 245789 := by norm_num

private theorem prime_oneHundredThreeCW_261281 : Nat.Prime 261281 := by norm_num

private theorem prime_oneHundredThreeCW_266153 : Nat.Prime 266153 := by norm_num

private theorem prime_oneHundredThreeCW_270953 : Nat.Prime 270953 := by norm_num

private theorem prime_oneHundredThreeCW_285533 : Nat.Prime 285533 := by norm_num

private theorem prime_oneHundredThreeCW_288317 : Nat.Prime 288317 := by norm_num

private theorem prime_oneHundredThreeCW_289019 : Nat.Prime 289019 := by norm_num

private theorem prime_oneHundredThreeCW_314747 : Nat.Prime 314747 := by norm_num

private theorem prime_oneHundredThreeCW_324799 : Nat.Prime 324799 := by norm_num

private theorem prime_oneHundredThreeCW_326083 : Nat.Prime 326083 := by norm_num

private theorem prime_oneHundredThreeCW_352619 : Nat.Prime 352619 := by norm_num

private theorem prime_oneHundredThreeCW_362293 : Nat.Prime 362293 := by norm_num

private theorem prime_oneHundredThreeCW_370421 : Nat.Prime 370421 := by norm_num

private theorem prime_oneHundredThreeCW_379541 : Nat.Prime 379541 := by norm_num

private theorem prime_oneHundredThreeCW_388573 : Nat.Prime 388573 := by norm_num

private theorem prime_oneHundredThreeCW_389297 : Nat.Prime 389297 := by norm_num

private theorem prime_oneHundredThreeCW_394787 : Nat.Prime 394787 := by norm_num

private theorem prime_oneHundredThreeCW_408817 : Nat.Prime 408817 := by norm_num

private theorem prime_oneHundredThreeCW_427067 : Nat.Prime 427067 := by norm_num

private theorem prime_oneHundredThreeCW_436483 : Nat.Prime 436483 := by norm_num

private theorem prime_oneHundredThreeCW_438203 : Nat.Prime 438203 := by norm_num

private theorem prime_oneHundredThreeCW_440333 : Nat.Prime 440333 := by norm_num

private theorem prime_oneHundredThreeCW_450503 : Nat.Prime 450503 := by norm_num

private theorem prime_oneHundredThreeCW_460387 : Nat.Prime 460387 := by norm_num

private theorem prime_oneHundredThreeCW_468289 : Nat.Prime 468289 := by norm_num

private theorem prime_oneHundredThreeCW_480541 : Nat.Prime 480541 := by norm_num

private theorem prime_oneHundredThreeCW_508517 : Nat.Prime 508517 := by norm_num

private theorem prime_oneHundredThreeCW_550267 : Nat.Prime 550267 := by norm_num

private theorem prime_oneHundredThreeCW_553103 : Nat.Prime 553103 := by norm_num

private theorem prime_oneHundredThreeCW_554597 : Nat.Prime 554597 := by norm_num

private theorem prime_oneHundredThreeCW_574859 : Nat.Prime 574859 := by norm_num

private theorem prime_oneHundredThreeCW_659353 : Nat.Prime 659353 := by norm_num

private theorem prime_oneHundredThreeCW_663709 : Nat.Prime 663709 := by norm_num

private theorem prime_oneHundredThreeCW_676661 : Nat.Prime 676661 := by norm_num

private theorem prime_oneHundredThreeCW_692689 : Nat.Prime 692689 := by norm_num

private theorem prime_oneHundredThreeCW_699401 : Nat.Prime 699401 := by norm_num

private theorem prime_oneHundredThreeCW_715373 : Nat.Prime 715373 := by norm_num

private theorem prime_oneHundredThreeCW_719713 : Nat.Prime 719713 := by norm_num

private theorem prime_oneHundredThreeCW_793327 : Nat.Prime 793327 := by norm_num

private theorem prime_oneHundredThreeCW_822631 : Nat.Prime 822631 := by norm_num

private theorem prime_oneHundredThreeCW_929161 : Nat.Prime 929161 := by norm_num

private theorem prime_oneHundredThreeCW_935513 : Nat.Prime 935513 := by norm_num

private theorem prime_oneHundredThreeCW_995959 : Nat.Prime 995959 := by norm_num

private theorem prime_oneHundredThreeCW_1017847 : Nat.Prime 1017847 := by norm_num

private theorem prime_oneHundredThreeCW_1042469 : Nat.Prime 1042469 := by norm_num

private theorem prime_oneHundredThreeCW_1065689 : Nat.Prime 1065689 := by norm_num

private theorem prime_oneHundredThreeCW_1122587 : Nat.Prime 1122587 := by norm_num

private theorem prime_oneHundredThreeCW_1157381 : Nat.Prime 1157381 := by norm_num

private theorem prime_oneHundredThreeCW_1175767 : Nat.Prime 1175767 := by norm_num

private theorem prime_oneHundredThreeCW_1230337 : Nat.Prime 1230337 := by norm_num

private theorem prime_oneHundredThreeCW_1413179 : Nat.Prime 1413179 := by norm_num

private theorem prime_oneHundredThreeCW_1450637 : Nat.Prime 1450637 := by norm_num

private theorem prime_oneHundredThreeCW_1597693 : Nat.Prime 1597693 := by norm_num

private theorem prime_oneHundredThreeCW_1611353 : Nat.Prime 1611353 := by norm_num

private theorem prime_oneHundredThreeCW_1623157 : Nat.Prime 1623157 := by norm_num

private theorem prime_oneHundredThreeCW_1722821 : Nat.Prime 1722821 := by norm_num

private theorem prime_oneHundredThreeCW_1897711 : Nat.Prime 1897711 := by norm_num

private theorem prime_oneHundredThreeCW_1988353 : Nat.Prime 1988353 := by norm_num

private theorem prime_oneHundredThreeCW_1996817 : Nat.Prime 1996817 := by norm_num

private theorem prime_oneHundredThreeCW_2043739 : Nat.Prime 2043739 := by norm_num

private theorem prime_oneHundredThreeCW_2242517 : Nat.Prime 2242517 := by norm_num

private theorem prime_oneHundredThreeCW_2312573 : Nat.Prime 2312573 := by norm_num

private theorem prime_oneHundredThreeCW_2314043 : Nat.Prime 2314043 := by norm_num

private theorem prime_oneHundredThreeCW_2557757 : Nat.Prime 2557757 := by norm_num

private theorem prime_oneHundredThreeCW_2606251 : Nat.Prime 2606251 := by norm_num

private theorem prime_oneHundredThreeCW_2629243 : Nat.Prime 2629243 := by norm_num

private theorem prime_oneHundredThreeCW_2670931 : Nat.Prime 2670931 := by norm_num

private theorem prime_oneHundredThreeCW_2698453 : Nat.Prime 2698453 := by norm_num

private theorem prime_oneHundredThreeCW_2709877 : Nat.Prime 2709877 := by norm_num

private theorem prime_oneHundredThreeCW_2715599 : Nat.Prime 2715599 := by norm_num

private theorem prime_oneHundredThreeCW_3160559 : Nat.Prime 3160559 := by norm_num

private theorem prime_oneHundredThreeCW_3207439 : Nat.Prime 3207439 := by norm_num

private theorem prime_oneHundredThreeCW_3557501 : Nat.Prime 3557501 := by norm_num

private theorem prime_oneHundredThreeCW_3623483 : Nat.Prime 3623483 := by norm_num

private theorem prime_oneHundredThreeCW_3874711 : Nat.Prime 3874711 := by norm_num

private theorem prime_oneHundredThreeCW_3909589 : Nat.Prime 3909589 := by norm_num

private theorem prime_oneHundredThreeCW_3927751 : Nat.Prime 3927751 := by norm_num

private theorem prime_oneHundredThreeCW_3999733 : Nat.Prime 3999733 := by norm_num

private theorem prime_oneHundredThreeCW_4073851 : Nat.Prime 4073851 := by norm_num

private theorem prime_oneHundredThreeCW_4109771 : Nat.Prime 4109771 := by norm_num

private theorem prime_oneHundredThreeCW_4196837 : Nat.Prime 4196837 := by norm_num

private theorem prime_oneHundredThreeCW_4412183 : Nat.Prime 4412183 := by norm_num

private theorem prime_oneHundredThreeCW_4451483 : Nat.Prime 4451483 := by norm_num

private theorem prime_oneHundredThreeCW_4571053 : Nat.Prime 4571053 := by norm_num

private theorem prime_oneHundredThreeCW_5165753 : Nat.Prime 5165753 := by norm_num

private theorem prime_oneHundredThreeCW_5251711 : Nat.Prime 5251711 := by norm_num

private theorem prime_oneHundredThreeCW_5272541 : Nat.Prime 5272541 := by norm_num

private theorem prime_oneHundredThreeCW_5351077 : Nat.Prime 5351077 := by norm_num

private theorem prime_oneHundredThreeCW_5463023 : Nat.Prime 5463023 := by norm_num

private theorem prime_oneHundredThreeCW_5695721 : Nat.Prime 5695721 := by norm_num

private theorem prime_oneHundredThreeCW_5837891 : Nat.Prime 5837891 := by norm_num

private theorem prime_oneHundredThreeCW_5888633 : Nat.Prime 5888633 := by norm_num

private theorem prime_oneHundredThreeCW_6104663 : Nat.Prime 6104663 := by norm_num

private theorem prime_oneHundredThreeCW_6295717 : Nat.Prime 6295717 := by norm_num

private theorem prime_oneHundredThreeCW_6322831 : Nat.Prime 6322831 := by norm_num

private theorem prime_oneHundredThreeCW_6698897 : Nat.Prime 6698897 := by norm_num

private theorem prime_oneHundredThreeCW_6723593 : Nat.Prime 6723593 := by norm_num

private theorem prime_oneHundredThreeCW_6814289 : Nat.Prime 6814289 := by norm_num

private theorem prime_oneHundredThreeCW_7074713 : Nat.Prime 7074713 := by norm_num

private theorem prime_oneHundredThreeCW_7496729 : Nat.Prime 7496729 := by norm_num

private theorem prime_oneHundredThreeCW_8038873 : Nat.Prime 8038873 := by norm_num

private theorem prime_oneHundredThreeCW_8606729 : Nat.Prime 8606729 := by norm_num

private theorem prime_oneHundredThreeCW_8970217 : Nat.Prime 8970217 := by norm_num

private theorem prime_oneHundredThreeCW_9527003 : Nat.Prime 9527003 := by norm_num

private theorem prime_oneHundredThreeCW_9582659 : Nat.Prime 9582659 := by norm_num

private theorem prime_oneHundredThreeCW_9757907 : Nat.Prime 9757907 := by norm_num

private theorem prime_oneHundredThreeCW_10592041 : Nat.Prime 10592041 := by norm_num

private theorem prime_oneHundredThreeCW_11101331 : Nat.Prime 11101331 := by norm_num

private theorem prime_oneHundredThreeCW_11274379 : Nat.Prime 11274379 := by norm_num

private theorem prime_oneHundredThreeCW_13672847 : Nat.Prime 13672847 := by norm_num

private theorem prime_oneHundredThreeCW_16369303 : Nat.Prime 16369303 := by norm_num

private theorem prime_oneHundredThreeCW_16953193 : Nat.Prime 16953193 := by norm_num

private theorem prime_oneHundredThreeCW_17756623 : Nat.Prime 17756623 := by norm_num

private theorem prime_oneHundredThreeCW_18547817 : Nat.Prime 18547817 := by norm_num

private theorem prime_oneHundredThreeCW_18858143 : Nat.Prime 18858143 := by norm_num

private theorem prime_oneHundredThreeCW_19357451 : Nat.Prime 19357451 := by norm_num

private theorem prime_oneHundredThreeCW_19676231 : Nat.Prime 19676231 := by norm_num

private theorem prime_oneHundredThreeCW_19750517 : Nat.Prime 19750517 := by norm_num

private theorem prime_oneHundredThreeCW_22310971 : Nat.Prime 22310971 := by norm_num

private theorem prime_oneHundredThreeCW_22420523 : Nat.Prime 22420523 := by norm_num

private theorem prime_oneHundredThreeCW_22701223 : Nat.Prime 22701223 := by norm_num

private theorem prime_oneHundredThreeCW_24407519 : Nat.Prime 24407519 := by norm_num

private theorem prime_oneHundredThreeCW_25067087 : Nat.Prime 25067087 := by norm_num

private theorem prime_oneHundredThreeCW_25180063 : Nat.Prime 25180063 := by norm_num

private theorem prime_oneHundredThreeCW_27530651 : Nat.Prime 27530651 := by norm_num

private theorem prime_oneHundredThreeCW_28260781 : Nat.Prime 28260781 := by norm_num

private theorem prime_oneHundredThreeCW_29807537 : Nat.Prime 29807537 := by norm_num

private theorem prime_oneHundredThreeCW_29871473 : Nat.Prime 29871473 := by norm_num

private theorem prime_oneHundredThreeCW_30471499 : Nat.Prime 30471499 := by
  apply lucas_primality 30471499 (2 : ZMod 30471499)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (101, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (101, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 30471499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_37
      · exact prime_oneHundredThreeCW_101
      · exact prime_oneHundredThreeCW_151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30471499) ^ 15235749 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30471499) ^ 10157166 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30471499) ^ 823554 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30471499) ^ 301698 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30471499) ^ 201798 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_31602959 : Nat.Prime 31602959 := by
  apply lucas_primality 31602959 (11 : ZMod 31602959)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (427067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (427067, 1)] : List FactorBlock).map factorBlockValue).prod) = 31602959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_37
      · exact prime_oneHundredThreeCW_427067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 31602959) ^ 15801479 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 31602959) ^ 854134 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 31602959) ^ 74 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_31700573 : Nat.Prime 31700573 := by
  apply lucas_primality 31700573 (2 : ZMod 31700573)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (149531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (149531, 1)] : List FactorBlock).map factorBlockValue).prod) = 31700573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_53
      · exact prime_oneHundredThreeCW_149531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31700573) ^ 15850286 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31700573) ^ 598124 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31700573) ^ 212 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_32106463 : Nat.Prime 32106463 := by
  apply lucas_primality 32106463 (5 : ZMod 32106463)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5351077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5351077, 1)] : List FactorBlock).map factorBlockValue).prod) = 32106463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5351077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 32106463) ^ 16053231 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 32106463) ^ 10702154 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 32106463) ^ 6 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_33172709 : Nat.Prime 33172709 := by
  apply lucas_primality 33172709 (2 : ZMod 33172709)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (436483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (436483, 1)] : List FactorBlock).map factorBlockValue).prod) = 33172709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_19
      · exact prime_oneHundredThreeCW_436483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33172709) ^ 16586354 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 33172709) ^ 1745932 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 33172709) ^ 76 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_37862963 : Nat.Prime 37862963 := by
  apply lucas_primality 37862963 (2 : ZMod 37862963)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (79, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (79, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) = 37862963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_43
      · exact prime_oneHundredThreeCW_79
      · exact prime_oneHundredThreeCW_5573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37862963) ^ 18931481 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 37862963) ^ 880534 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 37862963) ^ 479278 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 37862963) ^ 6794 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_41700017 : Nat.Prime 41700017 := by
  apply lucas_primality 41700017 (3 : ZMod 41700017)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2606251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2606251, 1)] : List FactorBlock).map factorBlockValue).prod) = 41700017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_2606251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 41700017) ^ 20850008 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41700017) ^ 16 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_41830279 : Nat.Prime 41830279 := by
  apply lucas_primality 41830279 (3 : ZMod 41830279)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (995959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (995959, 1)] : List FactorBlock).map factorBlockValue).prod) = 41830279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_995959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 41830279) ^ 20915139 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41830279) ^ 13943426 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41830279) ^ 5975754 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41830279) ^ 42 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_43481797 : Nat.Prime 43481797 := by
  apply lucas_primality 43481797 (2 : ZMod 43481797)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3623483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3623483, 1)] : List FactorBlock).map factorBlockValue).prod) = 43481797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_3623483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43481797) ^ 21740898 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 43481797) ^ 14493932 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 43481797) ^ 12 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_47923609 : Nat.Prime 47923609 := by
  apply lucas_primality 47923609 (11 : ZMod 47923609)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1996817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1996817, 1)] : List FactorBlock).map factorBlockValue).prod) = 47923609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_1996817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 47923609) ^ 23961804 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 47923609) ^ 15974536 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 47923609) ^ 24 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_49197947 : Nat.Prime 49197947 := by
  apply lucas_primality 49197947 (2 : ZMod 49197947)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (877, 1), (4007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (877, 1), (4007, 1)] : List FactorBlock).map factorBlockValue).prod) = 49197947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_877
      · exact prime_oneHundredThreeCW_4007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49197947) ^ 24598973 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 49197947) ^ 7028278 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 49197947) ^ 56098 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 49197947) ^ 12278 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_49823471 : Nat.Prime 49823471 := by
  apply lucas_primality 49823471 (11 : ZMod 49823471)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1543, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1543, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) = 49823471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_1543
      · exact prime_oneHundredThreeCW_3229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 49823471) ^ 24911735 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 49823471) ^ 9964694 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 49823471) ^ 32290 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 49823471) ^ 15430 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_50693309 : Nat.Prime 50693309 := by
  apply lucas_primality 50693309 (2 : ZMod 50693309)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (408817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (408817, 1)] : List FactorBlock).map factorBlockValue).prod) = 50693309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_408817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50693309) ^ 25346654 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 50693309) ^ 1635268 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 50693309) ^ 124 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_56872993 : Nat.Prime 56872993 := by
  apply lucas_primality 56872993 (10 : ZMod 56872993)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (53857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (53857, 1)] : List FactorBlock).map factorBlockValue).prod) = 56872993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_53857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 56872993) ^ 28436496 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (10 : ZMod 56872993) ^ 18957664 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (10 : ZMod 56872993) ^ 5170272 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (10 : ZMod 56872993) ^ 1056 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_60941369 : Nat.Prime 60941369 := by
  apply lucas_primality 60941369 (3 : ZMod 60941369)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (205883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (205883, 1)] : List FactorBlock).map factorBlockValue).prod) = 60941369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_37
      · exact prime_oneHundredThreeCW_205883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 60941369) ^ 30470684 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 60941369) ^ 1647064 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 60941369) ^ 296 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_63798727 : Nat.Prime 63798727 := by
  apply lucas_primality 63798727 (6 : ZMod 63798727)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (347, 1), (30643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (347, 1), (30643, 1)] : List FactorBlock).map factorBlockValue).prod) = 63798727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_347
      · exact prime_oneHundredThreeCW_30643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 63798727) ^ 31899363 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 63798727) ^ 21266242 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 63798727) ^ 183858 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 63798727) ^ 2082 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_65925731 : Nat.Prime 65925731 := by
  apply lucas_primality 65925731 (2 : ZMod 65925731)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (101, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (101, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) = 65925731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_101
      · exact prime_oneHundredThreeCW_5021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65925731) ^ 32962865 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 65925731) ^ 13185146 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 65925731) ^ 5071210 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 65925731) ^ 652730 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 65925731) ^ 13130 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_66224317 : Nat.Prime 66224317 := by
  apply lucas_primality 66224317 (2 : ZMod 66224317)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (47, 1), (6907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (47, 1), (6907, 1)] : List FactorBlock).map factorBlockValue).prod) = 66224317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_47
      · exact prime_oneHundredThreeCW_6907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66224317) ^ 33112158 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 66224317) ^ 22074772 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 66224317) ^ 3895548 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 66224317) ^ 1409028 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 66224317) ^ 9588 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_67103107 : Nat.Prime 67103107 := by
  apply lucas_primality 67103107 (2 : ZMod 67103107)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1597693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1597693, 1)] : List FactorBlock).map factorBlockValue).prod) = 67103107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_1597693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 67103107) ^ 33551553 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 67103107) ^ 22367702 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 67103107) ^ 9586158 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 67103107) ^ 42 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_82440737 : Nat.Prime 82440737 := by
  apply lucas_primality 82440737 (3 : ZMod 82440737)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 4), (29, 1), (37, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 4), (29, 1), (37, 1)] : List FactorBlock).map factorBlockValue).prod) = 82440737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_29
      · exact prime_oneHundredThreeCW_37
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 82440737) ^ 41220368 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 82440737) ^ 11777248 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 82440737) ^ 2842784 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 82440737) ^ 2228128 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_83305549 : Nat.Prime 83305549 := by
  apply lucas_primality 83305549 (2 : ZMod 83305549)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2314043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2314043, 1)] : List FactorBlock).map factorBlockValue).prod) = 83305549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_2314043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 83305549) ^ 41652774 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 83305549) ^ 27768516 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 83305549) ^ 36 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_86410523 : Nat.Prime 86410523 := by
  apply lucas_primality 86410523 (2 : ZMod 86410523)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3927751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3927751, 1)] : List FactorBlock).map factorBlockValue).prod) = 86410523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_3927751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86410523) ^ 43205261 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 86410523) ^ 7855502 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 86410523) ^ 22 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_95400047 : Nat.Prime 95400047 := by
  apply lucas_primality 95400047 (5 : ZMod 95400047)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (6814289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (6814289, 1)] : List FactorBlock).map factorBlockValue).prod) = 95400047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_6814289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 95400047) ^ 47700023 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 95400047) ^ 13628578 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 95400047) ^ 14 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_100634641 : Nat.Prime 100634641 := by
  apply lucas_primality 100634641 (31 : ZMod 100634641)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (29, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (29, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) = 100634641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_19
      · exact prime_oneHundredThreeCW_29
      · exact prime_oneHundredThreeCW_761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 100634641) ^ 50317320 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (31 : ZMod 100634641) ^ 33544880 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (31 : ZMod 100634641) ^ 20126928 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (31 : ZMod 100634641) ^ 5296560 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (31 : ZMod 100634641) ^ 3470160 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (31 : ZMod 100634641) ^ 132240 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_113054321 : Nat.Prime 113054321 := by
  apply lucas_primality 113054321 (3 : ZMod 113054321)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1413179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1413179, 1)] : List FactorBlock).map factorBlockValue).prod) = 113054321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_1413179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 113054321) ^ 56527160 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 113054321) ^ 22610864 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 113054321) ^ 80 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_116267101 : Nat.Prime 116267101 := by
  apply lucas_primality 116267101 (2 : ZMod 116267101)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (73, 1), (5309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (73, 1), (5309, 1)] : List FactorBlock).map factorBlockValue).prod) = 116267101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_73
      · exact prime_oneHundredThreeCW_5309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 116267101) ^ 58133550 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 116267101) ^ 38755700 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 116267101) ^ 23253420 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 116267101) ^ 1592700 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 116267101) ^ 21900 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_123090673 : Nat.Prime 123090673 := by
  apply lucas_primality 123090673 (5 : ZMod 123090673)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (97, 1), (26437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (97, 1), (26437, 1)] : List FactorBlock).map factorBlockValue).prod) = 123090673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_97
      · exact prime_oneHundredThreeCW_26437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 123090673) ^ 61545336 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 123090673) ^ 41030224 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 123090673) ^ 1268976 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 123090673) ^ 4656 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_125904913 : Nat.Prime 125904913 := by
  apply lucas_primality 125904913 (5 : ZMod 125904913)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (199, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (199, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) = 125904913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_199
      · exact prime_oneHundredThreeCW_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 125904913) ^ 62952456 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 125904913) ^ 41968304 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 125904913) ^ 17986416 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 125904913) ^ 632688 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 125904913) ^ 468048 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_129178067 : Nat.Prime 129178067 := by
  apply lucas_primality 129178067 (2 : ZMod 129178067)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (239, 1), (5099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (239, 1), (5099, 1)] : List FactorBlock).map factorBlockValue).prod) = 129178067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_53
      · exact prime_oneHundredThreeCW_239
      · exact prime_oneHundredThreeCW_5099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 129178067) ^ 64589033 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 129178067) ^ 2437322 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 129178067) ^ 540494 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 129178067) ^ 25334 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_139621541 : Nat.Prime 139621541 := by
  apply lucas_primality 139621541 (2 : ZMod 139621541)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2111, 1), (3307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2111, 1), (3307, 1)] : List FactorBlock).map factorBlockValue).prod) = 139621541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_2111
      · exact prime_oneHundredThreeCW_3307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139621541) ^ 69810770 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 139621541) ^ 27924308 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 139621541) ^ 66140 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 139621541) ^ 42220 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_153740329 : Nat.Prime 153740329 := by
  apply lucas_primality 153740329 (11 : ZMod 153740329)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (37, 1), (24733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (37, 1), (24733, 1)] : List FactorBlock).map factorBlockValue).prod) = 153740329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_37
      · exact prime_oneHundredThreeCW_24733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 153740329) ^ 76870164 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 153740329) ^ 51246776 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 153740329) ^ 21962904 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 153740329) ^ 4155144 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 153740329) ^ 6216 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_164912417 : Nat.Prime 164912417 := by
  apply lucas_primality 164912417 (3 : ZMod 164912417)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (97, 1), (53129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (97, 1), (53129, 1)] : List FactorBlock).map factorBlockValue).prod) = 164912417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_97
      · exact prime_oneHundredThreeCW_53129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 164912417) ^ 82456208 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 164912417) ^ 1700128 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 164912417) ^ 3104 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_182256391 : Nat.Prime 182256391 := by
  apply lucas_primality 182256391 (3 : ZMod 182256391)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (569, 1), (3559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (569, 1), (3559, 1)] : List FactorBlock).map factorBlockValue).prod) = 182256391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_569
      · exact prime_oneHundredThreeCW_3559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 182256391) ^ 91128195 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 182256391) ^ 60752130 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 182256391) ^ 36451278 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 182256391) ^ 320310 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 182256391) ^ 51210 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_187511953 : Nat.Prime 187511953 := by
  apply lucas_primality 187511953 (5 : ZMod 187511953)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (47, 1), (83117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (47, 1), (83117, 1)] : List FactorBlock).map factorBlockValue).prod) = 187511953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_47
      · exact prime_oneHundredThreeCW_83117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 187511953) ^ 93755976 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 187511953) ^ 62503984 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 187511953) ^ 3989616 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 187511953) ^ 2256 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_196925579 : Nat.Prime 196925579 := by
  apply lucas_primality 196925579 (2 : ZMod 196925579)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (383, 1), (8293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (383, 1), (8293, 1)] : List FactorBlock).map factorBlockValue).prod) = 196925579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_383
      · exact prime_oneHundredThreeCW_8293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 196925579) ^ 98462789 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 196925579) ^ 6352438 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 196925579) ^ 514166 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 196925579) ^ 23746 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_224514041 : Nat.Prime 224514041 := by
  apply lucas_primality 224514041 (3 : ZMod 224514041)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (277, 1), (881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (277, 1), (881, 1)] : List FactorBlock).map factorBlockValue).prod) = 224514041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_277
      · exact prime_oneHundredThreeCW_881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 224514041) ^ 112257020 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 224514041) ^ 44902808 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 224514041) ^ 9761480 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 224514041) ^ 810520 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 224514041) ^ 254840 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_225358697 : Nat.Prime 225358697 := by
  apply lucas_primality 225358697 (3 : ZMod 225358697)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (661, 1), (2243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (661, 1), (2243, 1)] : List FactorBlock).map factorBlockValue).prod) = 225358697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_19
      · exact prime_oneHundredThreeCW_661
      · exact prime_oneHundredThreeCW_2243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 225358697) ^ 112679348 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 225358697) ^ 11860984 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 225358697) ^ 340936 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 225358697) ^ 100472 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_226108643 : Nat.Prime 226108643 := by
  apply lucas_primality 226108643 (2 : ZMod 226108643)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113054321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113054321, 1)] : List FactorBlock).map factorBlockValue).prod) = 226108643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_113054321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 226108643) ^ 113054321 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 226108643) ^ 2 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_228471161 : Nat.Prime 228471161 := by
  apply lucas_primality 228471161 (3 : ZMod 228471161)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 1), (79, 1), (4253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 1), (79, 1), (4253, 1)] : List FactorBlock).map factorBlockValue).prod) = 228471161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_79
      · exact prime_oneHundredThreeCW_4253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 228471161) ^ 114235580 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 228471161) ^ 45694232 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 228471161) ^ 13439480 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 228471161) ^ 2892040 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 228471161) ^ 53720 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_333909701 : Nat.Prime 333909701 := by
  apply lucas_primality 333909701 (2 : ZMod 333909701)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (269, 1), (12413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (269, 1), (12413, 1)] : List FactorBlock).map factorBlockValue).prod) = 333909701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_269
      · exact prime_oneHundredThreeCW_12413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 333909701) ^ 166954850 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 333909701) ^ 66781940 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 333909701) ^ 1241300 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 333909701) ^ 26900 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_356692769 : Nat.Prime 356692769 := by
  apply lucas_primality 356692769 (3 : ZMod 356692769)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (439, 1), (25391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (439, 1), (25391, 1)] : List FactorBlock).map factorBlockValue).prod) = 356692769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_439
      · exact prime_oneHundredThreeCW_25391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 356692769) ^ 178346384 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 356692769) ^ 812512 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 356692769) ^ 14048 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_388389299 : Nat.Prime 388389299 := by
  apply lucas_primality 388389299 (2 : ZMod 388389299)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (929161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (929161, 1)] : List FactorBlock).map factorBlockValue).prod) = 388389299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_19
      · exact prime_oneHundredThreeCW_929161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 388389299) ^ 194194649 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 388389299) ^ 35308118 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 388389299) ^ 20441542 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 388389299) ^ 418 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_392110193 : Nat.Prime 392110193 := by
  apply lucas_primality 392110193 (3 : ZMod 392110193)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (163, 1), (251, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (163, 1), (251, 1), (599, 1)] : List FactorBlock).map factorBlockValue).prod) = 392110193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_163
      · exact prime_oneHundredThreeCW_251
      · exact prime_oneHundredThreeCW_599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 392110193) ^ 196055096 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 392110193) ^ 2405584 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 392110193) ^ 1562192 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 392110193) ^ 654608 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_398045651 : Nat.Prime 398045651 := by
  apply lucas_primality 398045651 (2 : ZMod 398045651)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (468289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (468289, 1)] : List FactorBlock).map factorBlockValue).prod) = 398045651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_468289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 398045651) ^ 199022825 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 398045651) ^ 79609130 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 398045651) ^ 23414450 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 398045651) ^ 850 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_427477097 : Nat.Prime 427477097 := by
  apply lucas_primality 427477097 (3 : ZMod 427477097)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (251, 1), (359, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (251, 1), (359, 1), (593, 1)] : List FactorBlock).map factorBlockValue).prod) = 427477097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_251
      · exact prime_oneHundredThreeCW_359
      · exact prime_oneHundredThreeCW_593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 427477097) ^ 213738548 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 427477097) ^ 1703096 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 427477097) ^ 1190744 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 427477097) ^ 720872 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_490452371 : Nat.Prime 490452371 := by
  apply lucas_primality 490452371 (2 : ZMod 490452371)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (97, 1), (421, 1), (1201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (97, 1), (421, 1), (1201, 1)] : List FactorBlock).map factorBlockValue).prod) = 490452371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_97
      · exact prime_oneHundredThreeCW_421
      · exact prime_oneHundredThreeCW_1201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 490452371) ^ 245226185 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 490452371) ^ 98090474 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 490452371) ^ 5056210 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 490452371) ^ 1164970 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 490452371) ^ 408370 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_518463139 : Nat.Prime 518463139 := by
  apply lucas_primality 518463139 (3 : ZMod 518463139)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (86410523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (86410523, 1)] : List FactorBlock).map factorBlockValue).prod) = 518463139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_86410523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 518463139) ^ 259231569 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 518463139) ^ 172821046 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 518463139) ^ 6 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_542745347 : Nat.Prime 542745347 := by
  apply lucas_primality 542745347 (2 : ZMod 542745347)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (1897711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (1897711, 1)] : List FactorBlock).map factorBlockValue).prod) = 542745347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_1897711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 542745347) ^ 271372673 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 542745347) ^ 49340486 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 542745347) ^ 41749642 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 542745347) ^ 286 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_598413581 : Nat.Prime 598413581 := by
  apply lucas_primality 598413581 (2 : ZMod 598413581)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37, 1), (317, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37, 1), (317, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) = 598413581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_37
      · exact prime_oneHundredThreeCW_317
      · exact prime_oneHundredThreeCW_2551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 598413581) ^ 299206790 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 598413581) ^ 119682716 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 598413581) ^ 16173340 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 598413581) ^ 1887740 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 598413581) ^ 234580 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_619018703 : Nat.Prime 619018703 := by
  apply lucas_primality 619018703 (5 : ZMod 619018703)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1493, 1), (207307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1493, 1), (207307, 1)] : List FactorBlock).map factorBlockValue).prod) = 619018703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_1493
      · exact prime_oneHundredThreeCW_207307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 619018703) ^ 309509351 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 619018703) ^ 414614 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 619018703) ^ 2986 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_700610311 : Nat.Prime 700610311 := by
  apply lucas_primality 700610311 (3 : ZMod 700610311)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (288317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (288317, 1)] : List FactorBlock).map factorBlockValue).prod) = 700610311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_288317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 700610311) ^ 350305155 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 700610311) ^ 233536770 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 700610311) ^ 140122062 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 700610311) ^ 2430 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_713385539 : Nat.Prime 713385539 := by
  apply lucas_primality 713385539 (2 : ZMod 713385539)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (356692769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (356692769, 1)] : List FactorBlock).map factorBlockValue).prod) = 713385539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_356692769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 713385539) ^ 356692769 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 713385539) ^ 2 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_776778599 : Nat.Prime 776778599 := by
  apply lucas_primality 776778599 (7 : ZMod 776778599)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (388389299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (388389299, 1)] : List FactorBlock).map factorBlockValue).prod) = 776778599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_388389299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 776778599) ^ 388389299 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 776778599) ^ 2 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_881534419 : Nat.Prime 881534419 := by
  apply lucas_primality 881534419 (14 : ZMod 881534419)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (197, 1), (467, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (197, 1), (467, 1), (1597, 1)] : List FactorBlock).map factorBlockValue).prod) = 881534419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_197
      · exact prime_oneHundredThreeCW_467
      · exact prime_oneHundredThreeCW_1597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 881534419) ^ 440767209 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 881534419) ^ 293844806 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 881534419) ^ 4474794 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 881534419) ^ 1887654 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 881534419) ^ 551994 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_937845581 : Nat.Prime 937845581 := by
  apply lucas_primality 937845581 (2 : ZMod 937845581)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (6698897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (6698897, 1)] : List FactorBlock).map factorBlockValue).prod) = 937845581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_6698897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 937845581) ^ 468922790 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 937845581) ^ 187569116 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 937845581) ^ 133977940 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 937845581) ^ 140 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_958635779 : Nat.Prime 958635779 := by
  apply lucas_primality 958635779 (2 : ZMod 958635779)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (379, 1), (7573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (379, 1), (7573, 1)] : List FactorBlock).map factorBlockValue).prod) = 958635779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_167
      · exact prime_oneHundredThreeCW_379
      · exact prime_oneHundredThreeCW_7573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 958635779) ^ 479317889 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 958635779) ^ 5740334 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 958635779) ^ 2529382 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 958635779) ^ 126586 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1169867779 : Nat.Prime 1169867779 := by
  apply lucas_primality 1169867779 (2 : ZMod 1169867779)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (2670931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (2670931, 1)] : List FactorBlock).map factorBlockValue).prod) = 1169867779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_73
      · exact prime_oneHundredThreeCW_2670931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1169867779) ^ 584933889 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1169867779) ^ 389955926 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1169867779) ^ 16025586 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1169867779) ^ 438 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1195063763 : Nat.Prime 1195063763 := by
  apply lucas_primality 1195063763 (2 : ZMod 1195063763)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (59, 1), (440333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (59, 1), (440333, 1)] : List FactorBlock).map factorBlockValue).prod) = 1195063763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_59
      · exact prime_oneHundredThreeCW_440333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1195063763) ^ 597531881 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1195063763) ^ 51959294 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1195063763) ^ 20255318 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1195063763) ^ 2714 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1238037407 : Nat.Prime 1238037407 := by
  apply lucas_primality 1238037407 (5 : ZMod 1238037407)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (619018703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (619018703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1238037407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_619018703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1238037407) ^ 619018703 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1238037407) ^ 2 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1238988809 : Nat.Prime 1238988809 := by
  apply lucas_primality 1238988809 (3 : ZMod 1238988809)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (37, 2), (47, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (37, 2), (47, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) = 1238988809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_29
      · exact prime_oneHundredThreeCW_37
      · exact prime_oneHundredThreeCW_47
      · exact prime_oneHundredThreeCW_83
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1238988809) ^ 619494404 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238988809) ^ 42723752 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238988809) ^ 33486184 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238988809) ^ 26361464 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1238988809) ^ 14927576 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1345528889 : Nat.Prime 1345528889 := by
  apply lucas_primality 1345528889 (3 : ZMod 1345528889)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (23, 1), (229, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (23, 1), (229, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) = 1345528889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_229
      · exact prime_oneHundredThreeCW_2903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1345528889) ^ 672764444 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1345528889) ^ 122320808 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1345528889) ^ 58501256 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1345528889) ^ 5875672 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1345528889) ^ 463496 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1347084247 : Nat.Prime 1347084247 := by
  apply lucas_primality 1347084247 (5 : ZMod 1347084247)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (224514041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (224514041, 1)] : List FactorBlock).map factorBlockValue).prod) = 1347084247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_224514041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1347084247) ^ 673542123 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1347084247) ^ 449028082 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1347084247) ^ 6 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1366106981 : Nat.Prime 1366106981 := by
  apply lucas_primality 1366106981 (2 : ZMod 1366106981)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (9757907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (9757907, 1)] : List FactorBlock).map factorBlockValue).prod) = 1366106981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_9757907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1366106981) ^ 683053490 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366106981) ^ 273221396 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366106981) ^ 195158140 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366106981) ^ 140 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1369044757 : Nat.Prime 1369044757 := by
  apply lucas_primality 1369044757 (2 : ZMod 1369044757)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4153, 1), (9157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4153, 1), (9157, 1)] : List FactorBlock).map factorBlockValue).prod) = 1369044757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_4153
      · exact prime_oneHundredThreeCW_9157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1369044757) ^ 684522378 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1369044757) ^ 456348252 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1369044757) ^ 329652 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1369044757) ^ 149508 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1599384439 : Nat.Prime 1599384439 := by
  apply lucas_primality 1599384439 (6 : ZMod 1599384439)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (193, 1), (460387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (193, 1), (460387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1599384439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_193
      · exact prime_oneHundredThreeCW_460387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1599384439) ^ 799692219 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1599384439) ^ 533128146 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1599384439) ^ 8286966 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1599384439) ^ 3474 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2079544127 : Nat.Prime 2079544127 := by
  apply lucas_primality 2079544127 (5 : ZMod 2079544127)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (4109771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (4109771, 1)] : List FactorBlock).map factorBlockValue).prod) = 2079544127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_4109771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2079544127) ^ 1039772063 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2079544127) ^ 189049466 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2079544127) ^ 90414962 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2079544127) ^ 506 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2232564599 : Nat.Prime 2232564599 := by
  apply lucas_primality 2232564599 (13 : ZMod 2232564599)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (4412183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (4412183, 1)] : List FactorBlock).map factorBlockValue).prod) = 2232564599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_4412183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2232564599) ^ 1116282299 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (13 : ZMod 2232564599) ^ 202960418 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (13 : ZMod 2232564599) ^ 97068026 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (13 : ZMod 2232564599) ^ 506 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2334899753 : Nat.Prime 2334899753 := by
  apply lucas_primality 2334899753 (3 : ZMod 2334899753)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (383, 1), (10733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (383, 1), (10733, 1)] : List FactorBlock).map factorBlockValue).prod) = 2334899753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_71
      · exact prime_oneHundredThreeCW_383
      · exact prime_oneHundredThreeCW_10733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2334899753) ^ 1167449876 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2334899753) ^ 32885912 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2334899753) ^ 6096344 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2334899753) ^ 217544 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2470218071 : Nat.Prime 2470218071 := by
  apply lucas_primality 2470218071 (17 : ZMod 2470218071)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12853, 1), (19219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12853, 1), (19219, 1)] : List FactorBlock).map factorBlockValue).prod) = 2470218071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_12853
      · exact prime_oneHundredThreeCW_19219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 2470218071) ^ 1235109035 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 2470218071) ^ 494043614 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 2470218071) ^ 192190 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 2470218071) ^ 128530 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2579715049 : Nat.Prime 2579715049 := by
  apply lucas_primality 2579715049 (11 : ZMod 2579715049)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (6322831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (6322831, 1)] : List FactorBlock).map factorBlockValue).prod) = 2579715049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_6322831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2579715049) ^ 1289857524 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2579715049) ^ 859905016 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2579715049) ^ 151747944 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2579715049) ^ 408 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_3368237623 : Nat.Prime 3368237623 := by
  apply lucas_primality 3368237623 (3 : ZMod 3368237623)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (24407519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (24407519, 1)] : List FactorBlock).map factorBlockValue).prod) = 3368237623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_24407519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3368237623) ^ 1684118811 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3368237623) ^ 1122745874 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3368237623) ^ 146445114 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3368237623) ^ 138 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_3720534281 : Nat.Prime 3720534281 := by
  apply lucas_primality 3720534281 (6 : ZMod 3720534281)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (53, 1), (76303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (53, 1), (76303, 1)] : List FactorBlock).map factorBlockValue).prod) = 3720534281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_53
      · exact prime_oneHundredThreeCW_76303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3720534281) ^ 1860267140 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3720534281) ^ 744106856 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3720534281) ^ 161762360 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3720534281) ^ 70198760 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3720534281) ^ 48760 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_3942263491 : Nat.Prime 3942263491 := by
  apply lucas_primality 3942263491 (2 : ZMod 3942263491)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 2), (31, 1), (53, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 2), (31, 1), (53, 1), (661, 1)] : List FactorBlock).map factorBlockValue).prod) = 3942263491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_53
      · exact prime_oneHundredThreeCW_661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3942263491) ^ 1971131745 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3942263491) ^ 1314087830 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3942263491) ^ 788452698 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3942263491) ^ 358387590 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3942263491) ^ 127169790 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3942263491) ^ 74382330 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3942263491) ^ 5964090 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_4290646421 : Nat.Prime 4290646421 := by
  apply lucas_primality 4290646421 (7 : ZMod 4290646421)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (79, 1), (2715599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (79, 1), (2715599, 1)] : List FactorBlock).map factorBlockValue).prod) = 4290646421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_79
      · exact prime_oneHundredThreeCW_2715599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4290646421) ^ 2145323210 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4290646421) ^ 858129284 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4290646421) ^ 54311980 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4290646421) ^ 1580 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_5014764731 : Nat.Prime 5014764731 := by
  apply lucas_primality 5014764731 (2 : ZMod 5014764731)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (701, 1), (715373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (701, 1), (715373, 1)] : List FactorBlock).map factorBlockValue).prod) = 5014764731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_701
      · exact prime_oneHundredThreeCW_715373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5014764731) ^ 2507382365 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5014764731) ^ 1002952946 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5014764731) ^ 7153730 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5014764731) ^ 7010 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_5197249177 : Nat.Prime 5197249177 := by
  apply lucas_primality 5197249177 (5 : ZMod 5197249177)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (1013, 1), (30539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (1013, 1), (30539, 1)] : List FactorBlock).map factorBlockValue).prod) = 5197249177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_1013
      · exact prime_oneHundredThreeCW_30539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5197249177) ^ 2598624588 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5197249177) ^ 1732416392 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5197249177) ^ 742464168 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5197249177) ^ 5130552 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5197249177) ^ 170184 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_6140414729 : Nat.Prime 6140414729 := by
  apply lucas_primality 6140414729 (3 : ZMod 6140414729)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (163, 2), (4127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (163, 2), (4127, 1)] : List FactorBlock).map factorBlockValue).prod) = 6140414729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_163
      · exact prime_oneHundredThreeCW_4127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6140414729) ^ 3070207364 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6140414729) ^ 877202104 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6140414729) ^ 37671256 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6140414729) ^ 1487864 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_7170382579 : Nat.Prime 7170382579 := by
  apply lucas_primality 7170382579 (2 : ZMod 7170382579)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1195063763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1195063763, 1)] : List FactorBlock).map factorBlockValue).prod) = 7170382579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_1195063763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7170382579) ^ 3585191289 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7170382579) ^ 2390127526 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7170382579) ^ 6 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_7654768423 : Nat.Prime 7654768423 := by
  apply lucas_primality 7654768423 (3 : ZMod 7654768423)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (182256391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (182256391, 1)] : List FactorBlock).map factorBlockValue).prod) = 7654768423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_182256391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7654768423) ^ 3827384211 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7654768423) ^ 2551589474 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7654768423) ^ 1093538346 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7654768423) ^ 42 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_8806539227 : Nat.Prime 8806539227 := by
  apply lucas_primality 8806539227 (2 : ZMod 8806539227)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (38707, 1), (113759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (38707, 1), (113759, 1)] : List FactorBlock).map factorBlockValue).prod) = 8806539227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_38707
      · exact prime_oneHundredThreeCW_113759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8806539227) ^ 4403269613 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8806539227) ^ 227518 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8806539227) ^ 77414 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_9601559269 : Nat.Prime 9601559269 := by
  apply lucas_primality 9601559269 (2 : ZMod 9601559269)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (43, 1), (271, 1), (577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (43, 1), (271, 1), (577, 1)] : List FactorBlock).map factorBlockValue).prod) = 9601559269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_43
      · exact prime_oneHundredThreeCW_271
      · exact prime_oneHundredThreeCW_577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9601559269) ^ 4800779634 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9601559269) ^ 3200519756 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9601559269) ^ 1371651324 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9601559269) ^ 564797604 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9601559269) ^ 223292076 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9601559269) ^ 35430108 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9601559269) ^ 16640484 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_11696534309 : Nat.Prime 11696534309 := by
  apply lucas_primality 11696534309 (2 : ZMod 11696534309)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (479, 1), (6104663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (479, 1), (6104663, 1)] : List FactorBlock).map factorBlockValue).prod) = 11696534309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_479
      · exact prime_oneHundredThreeCW_6104663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11696534309) ^ 5848267154 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11696534309) ^ 24418652 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11696534309) ^ 1916 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_11782475993 : Nat.Prime 11782475993 := by
  apply lucas_primality 11782475993 (3 : ZMod 11782475993)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11593, 1), (18149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11593, 1), (18149, 1)] : List FactorBlock).map factorBlockValue).prod) = 11782475993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_11593
      · exact prime_oneHundredThreeCW_18149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11782475993) ^ 5891237996 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 11782475993) ^ 1683210856 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 11782475993) ^ 1016344 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 11782475993) ^ 649208 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_11953978237 : Nat.Prime 11953978237 := by
  apply lucas_primality 11953978237 (5 : ZMod 11953978237)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (167, 1), (1988353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (167, 1), (1988353, 1)] : List FactorBlock).map factorBlockValue).prod) = 11953978237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_167
      · exact prime_oneHundredThreeCW_1988353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11953978237) ^ 5976989118 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 11953978237) ^ 3984659412 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 11953978237) ^ 71580708 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 11953978237) ^ 6012 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_12588875119 : Nat.Prime 12588875119 := by
  apply lucas_primality 12588875119 (3 : ZMod 12588875119)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (29, 1), (8038873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (29, 1), (8038873, 1)] : List FactorBlock).map factorBlockValue).prod) = 12588875119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_29
      · exact prime_oneHundredThreeCW_8038873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12588875119) ^ 6294437559 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12588875119) ^ 4196291706 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12588875119) ^ 434099142 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12588875119) ^ 1566 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_13092318737 : Nat.Prime 13092318737 := by
  apply lucas_primality 13092318737 (3 : ZMod 13092318737)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (61, 1), (73, 1), (26251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (61, 1), (73, 1), (26251, 1)] : List FactorBlock).map factorBlockValue).prod) = 13092318737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_61
      · exact prime_oneHundredThreeCW_73
      · exact prime_oneHundredThreeCW_26251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13092318737) ^ 6546159368 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13092318737) ^ 1870331248 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13092318737) ^ 214628176 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13092318737) ^ 179346832 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 13092318737) ^ 498736 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_18837404447 : Nat.Prime 18837404447 := by
  apply lucas_primality 18837404447 (10 : ZMod 18837404447)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1345528889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1345528889, 1)] : List FactorBlock).map factorBlockValue).prod) = 18837404447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_1345528889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 18837404447) ^ 9418702223 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (10 : ZMod 18837404447) ^ 2691057778 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (10 : ZMod 18837404447) ^ 14 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_18938884889 : Nat.Prime 18938884889 := by
  apply lucas_primality 18938884889 (3 : ZMod 18938884889)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (83, 1), (370421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (83, 1), (370421, 1)] : List FactorBlock).map factorBlockValue).prod) = 18938884889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_83
      · exact prime_oneHundredThreeCW_370421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18938884889) ^ 9469442444 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 18938884889) ^ 2705554984 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 18938884889) ^ 1721716808 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 18938884889) ^ 228179336 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 18938884889) ^ 51128 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_20209425739 : Nat.Prime 20209425739 := by
  apply lucas_primality 20209425739 (2 : ZMod 20209425739)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3368237623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3368237623, 1)] : List FactorBlock).map factorBlockValue).prod) = 20209425739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_3368237623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20209425739) ^ 10104712869 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20209425739) ^ 6736475246 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20209425739) ^ 6 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_20337243691 : Nat.Prime 20337243691 := by
  apply lucas_primality 20337243691 (2 : ZMod 20337243691)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3109, 1), (218047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3109, 1), (218047, 1)] : List FactorBlock).map factorBlockValue).prod) = 20337243691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_3109
      · exact prime_oneHundredThreeCW_218047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20337243691) ^ 10168621845 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20337243691) ^ 6779081230 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20337243691) ^ 4067448738 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20337243691) ^ 6541410 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20337243691) ^ 93270 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_23564951987 : Nat.Prime 23564951987 := by
  apply lucas_primality 23564951987 (2 : ZMod 23564951987)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11782475993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11782475993, 1)] : List FactorBlock).map factorBlockValue).prod) = 23564951987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11782475993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 23564951987) ^ 11782475993 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23564951987) ^ 2 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_24834870941 : Nat.Prime 24834870941 := by
  apply lucas_primality 24834870941 (2 : ZMod 24834870941)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (29, 1), (439, 1), (8867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (29, 1), (439, 1), (8867, 1)] : List FactorBlock).map factorBlockValue).prod) = 24834870941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_29
      · exact prime_oneHundredThreeCW_439
      · exact prime_oneHundredThreeCW_8867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24834870941) ^ 12417435470 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24834870941) ^ 4966974188 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24834870941) ^ 2257715540 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24834870941) ^ 856374860 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24834870941) ^ 56571460 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24834870941) ^ 2800820 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_33906857041 : Nat.Prime 33906857041 := by
  apply lucas_primality 33906857041 (11 : ZMod 33906857041)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (7, 1), (2242517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (7, 1), (2242517, 1)] : List FactorBlock).map factorBlockValue).prod) = 33906857041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_2242517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 33906857041) ^ 16953428520 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 33906857041) ^ 11302285680 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 33906857041) ^ 6781371408 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 33906857041) ^ 4843836720 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 33906857041) ^ 15120 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_35469039883 : Nat.Prime 35469039883 := by
  apply lucas_primality 35469039883 (2 : ZMod 35469039883)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (89, 1), (935513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (89, 1), (935513, 1)] : List FactorBlock).map factorBlockValue).prod) = 35469039883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_71
      · exact prime_oneHundredThreeCW_89
      · exact prime_oneHundredThreeCW_935513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35469039883) ^ 17734519941 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35469039883) ^ 11823013294 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35469039883) ^ 499563942 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35469039883) ^ 398528538 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35469039883) ^ 37914 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_38893463929 : Nat.Prime 38893463929 := by
  apply lucas_primality 38893463929 (7 : ZMod 38893463929)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (11, 1), (16369303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (11, 1), (16369303, 1)] : List FactorBlock).map factorBlockValue).prod) = 38893463929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_16369303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 38893463929) ^ 19446731964 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 38893463929) ^ 12964487976 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 38893463929) ^ 3535769448 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 38893463929) ^ 2376 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_44588426513 : Nat.Prime 44588426513 := by
  apply lucas_primality 44588426513 (3 : ZMod 44588426513)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (56872993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (56872993, 1)] : List FactorBlock).map factorBlockValue).prod) = 44588426513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_56872993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 44588426513) ^ 22294213256 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 44588426513) ^ 6369775216 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 44588426513) ^ 784 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_50355500477 : Nat.Prime 50355500477 := by
  apply lucas_primality 50355500477 (2 : ZMod 50355500477)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (12588875119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (12588875119, 1)] : List FactorBlock).map factorBlockValue).prod) = 50355500477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_12588875119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 50355500477) ^ 25177750238 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 50355500477) ^ 4 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_75412159499 : Nat.Prime 75412159499 := by
  apply lucas_primality 75412159499 (2 : ZMod 75412159499)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (337, 1), (8606729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (337, 1), (8606729, 1)] : List FactorBlock).map factorBlockValue).prod) = 75412159499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_337
      · exact prime_oneHundredThreeCW_8606729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75412159499) ^ 37706079749 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 75412159499) ^ 5800935346 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 75412159499) ^ 223774954 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 75412159499) ^ 8762 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_79458166523 : Nat.Prime 79458166523 := by
  apply lucas_primality 79458166523 (2 : ZMod 79458166523)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (2141, 1), (85513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (2141, 1), (85513, 1)] : List FactorBlock).map factorBlockValue).prod) = 79458166523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_2141
      · exact prime_oneHundredThreeCW_85513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79458166523) ^ 39729083261 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 79458166523) ^ 11351166646 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 79458166523) ^ 2563166662 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 79458166523) ^ 37112642 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 79458166523) ^ 929194 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_87694199657 : Nat.Prime 87694199657 := by
  apply lucas_primality 87694199657 (3 : ZMod 87694199657)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (43, 1), (167, 1), (31153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (43, 1), (167, 1), (31153, 1)] : List FactorBlock).map factorBlockValue).prod) = 87694199657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_43
      · exact prime_oneHundredThreeCW_167
      · exact prime_oneHundredThreeCW_31153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87694199657) ^ 43847099828 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 87694199657) ^ 12527742808 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 87694199657) ^ 2039399992 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 87694199657) ^ 525114968 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 87694199657) ^ 2814952 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_88509358867 : Nat.Prime 88509358867 := by
  apply lucas_primality 88509358867 (2 : ZMod 88509358867)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61979, 1), (238009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61979, 1), (238009, 1)] : List FactorBlock).map factorBlockValue).prod) = 88509358867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_61979
      · exact prime_oneHundredThreeCW_238009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 88509358867) ^ 44254679433 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 88509358867) ^ 29503119622 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 88509358867) ^ 1428054 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 88509358867) ^ 371874 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_91079340431 : Nat.Prime 91079340431 := by
  apply lucas_primality 91079340431 (7 : ZMod 91079340431)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (700610311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (700610311, 1)] : List FactorBlock).map factorBlockValue).prod) = 91079340431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_700610311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 91079340431) ^ 45539670215 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 91079340431) ^ 18215868086 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 91079340431) ^ 7006103110 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 91079340431) ^ 130 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_94576316629 : Nat.Prime 94576316629 := by
  apply lucas_primality 94576316629 (2 : ZMod 94576316629)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (313, 1), (25180063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (313, 1), (25180063, 1)] : List FactorBlock).map factorBlockValue).prod) = 94576316629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_313
      · exact prime_oneHundredThreeCW_25180063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94576316629) ^ 47288158314 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 94576316629) ^ 31525438876 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 94576316629) ^ 302160756 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 94576316629) ^ 3756 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_98731854929 : Nat.Prime 98731854929 := by
  apply lucas_primality 98731854929 (3 : ZMod 98731854929)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (881534419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (881534419, 1)] : List FactorBlock).map factorBlockValue).prod) = 98731854929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_881534419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 98731854929) ^ 49365927464 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 98731854929) ^ 14104550704 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 98731854929) ^ 112 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_101580237653 : Nat.Prime 101580237653 := by
  apply lucas_primality 101580237653 (3 : ZMod 101580237653)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (1907, 1), (324799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (1907, 1), (324799, 1)] : List FactorBlock).map factorBlockValue).prod) = 101580237653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_41
      · exact prime_oneHundredThreeCW_1907
      · exact prime_oneHundredThreeCW_324799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101580237653) ^ 50790118826 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 101580237653) ^ 2477566772 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 101580237653) ^ 53267036 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 101580237653) ^ 312748 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_109543000817 : Nat.Prime 109543000817 := by
  apply lucas_primality 109543000817 (3 : ZMod 109543000817)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (53, 1), (129178067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (53, 1), (129178067, 1)] : List FactorBlock).map factorBlockValue).prod) = 109543000817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_53
      · exact prime_oneHundredThreeCW_129178067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 109543000817) ^ 54771500408 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 109543000817) ^ 2066849072 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 109543000817) ^ 848 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_112090413311 : Nat.Prime 112090413311 := by
  apply lucas_primality 112090413311 (13 : ZMod 112090413311)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (131, 1), (2312573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (131, 1), (2312573, 1)] : List FactorBlock).map factorBlockValue).prod) = 112090413311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_37
      · exact prime_oneHundredThreeCW_131
      · exact prime_oneHundredThreeCW_2312573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 112090413311) ^ 56045206655 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (13 : ZMod 112090413311) ^ 22418082662 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (13 : ZMod 112090413311) ^ 3029470630 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (13 : ZMod 112090413311) ^ 855652010 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (13 : ZMod 112090413311) ^ 48470 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_115559271071 : Nat.Prime 115559271071 := by
  apply lucas_primality 115559271071 (17 : ZMod 115559271071)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (461, 1), (25067087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (461, 1), (25067087, 1)] : List FactorBlock).map factorBlockValue).prod) = 115559271071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_461
      · exact prime_oneHundredThreeCW_25067087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 115559271071) ^ 57779635535 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 115559271071) ^ 23111854214 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 115559271071) ^ 250670870 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 115559271071) ^ 4610 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_118355048719 : Nat.Prime 118355048719 := by
  apply lucas_primality 118355048719 (3 : ZMod 118355048719)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1151, 1), (1697, 1), (10099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1151, 1), (1697, 1), (10099, 1)] : List FactorBlock).map factorBlockValue).prod) = 118355048719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_1151
      · exact prime_oneHundredThreeCW_1697
      · exact prime_oneHundredThreeCW_10099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 118355048719) ^ 59177524359 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 118355048719) ^ 39451682906 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 118355048719) ^ 102828018 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 118355048719) ^ 69743694 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 118355048719) ^ 11719482 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_123291549179 : Nat.Prime 123291549179 := by
  apply lucas_primality 123291549179 (2 : ZMod 123291549179)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (8806539227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (8806539227, 1)] : List FactorBlock).map factorBlockValue).prod) = 123291549179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_8806539227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 123291549179) ^ 61645774589 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 123291549179) ^ 17613078454 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 123291549179) ^ 14 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_142976478569 : Nat.Prime 142976478569 := by
  apply lucas_primality 142976478569 (3 : ZMod 142976478569)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (1747, 1), (132859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (1747, 1), (132859, 1)] : List FactorBlock).map factorBlockValue).prod) = 142976478569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_1747
      · exact prime_oneHundredThreeCW_132859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 142976478569) ^ 71488239284 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 142976478569) ^ 20425211224 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 142976478569) ^ 12997861688 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 142976478569) ^ 81841144 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 142976478569) ^ 1076152 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_143477856971 : Nat.Prime 143477856971 := by
  apply lucas_primality 143477856971 (6 : ZMod 143477856971)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 3), (41830279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 3), (41830279, 1)] : List FactorBlock).map factorBlockValue).prod) = 143477856971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_41830279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 143477856971) ^ 71738928485 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 143477856971) ^ 28695571394 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 143477856971) ^ 20496836710 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 143477856971) ^ 3430 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_156889133309 : Nat.Prime 156889133309 := by
  apply lucas_primality 156889133309 (2 : ZMod 156889133309)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (251, 1), (3511, 1), (44507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (251, 1), (3511, 1), (44507, 1)] : List FactorBlock).map factorBlockValue).prod) = 156889133309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_251
      · exact prime_oneHundredThreeCW_3511
      · exact prime_oneHundredThreeCW_44507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 156889133309) ^ 78444566654 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 156889133309) ^ 625056308 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 156889133309) ^ 44685028 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 156889133309) ^ 3525044 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_166532169763 : Nat.Prime 166532169763 := by
  apply lucas_primality 166532169763 (2 : ZMod 166532169763)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (17, 1), (269, 1), (289019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (17, 1), (269, 1), (289019, 1)] : List FactorBlock).map factorBlockValue).prod) = 166532169763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_269
      · exact prime_oneHundredThreeCW_289019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 166532169763) ^ 83266084881 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 166532169763) ^ 55510723254 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 166532169763) ^ 23790309966 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 166532169763) ^ 9796009986 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 166532169763) ^ 619078698 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 166532169763) ^ 576198 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_177304208623 : Nat.Prime 177304208623 := by
  apply lucas_primality 177304208623 (3 : ZMod 177304208623)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (111029, 1), (266153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (111029, 1), (266153, 1)] : List FactorBlock).map factorBlockValue).prod) = 177304208623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_111029
      · exact prime_oneHundredThreeCW_266153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 177304208623) ^ 88652104311 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 177304208623) ^ 59101402874 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 177304208623) ^ 1596918 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 177304208623) ^ 666174 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_185344245959 : Nat.Prime 185344245959 := by
  apply lucas_primality 185344245959 (11 : ZMod 185344245959)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (11953, 1), (68611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (11953, 1), (68611, 1)] : List FactorBlock).map factorBlockValue).prod) = 185344245959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_113
      · exact prime_oneHundredThreeCW_11953
      · exact prime_oneHundredThreeCW_68611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 185344245959) ^ 92672122979 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 185344245959) ^ 1640214566 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 185344245959) ^ 15506086 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 185344245959) ^ 2701378 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_186410124179 : Nat.Prime 186410124179 := by
  apply lucas_primality 186410124179 (2 : ZMod 186410124179)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2903, 1), (32106463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2903, 1), (32106463, 1)] : List FactorBlock).map factorBlockValue).prod) = 186410124179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_2903
      · exact prime_oneHundredThreeCW_32106463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 186410124179) ^ 93205062089 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 186410124179) ^ 64212926 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 186410124179) ^ 5806 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_209444753351 : Nat.Prime 209444753351 := by
  apply lucas_primality 209444753351 (7 : ZMod 209444753351)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (598413581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (598413581, 1)] : List FactorBlock).map factorBlockValue).prod) = 209444753351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_598413581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 209444753351) ^ 104722376675 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 209444753351) ^ 41888950670 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 209444753351) ^ 29920679050 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 209444753351) ^ 350 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_264360628319 : Nat.Prime 264360628319 := by
  apply lucas_primality 264360628319 (7 : ZMod 264360628319)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25169, 1), (5251711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25169, 1), (5251711, 1)] : List FactorBlock).map factorBlockValue).prod) = 264360628319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_25169
      · exact prime_oneHundredThreeCW_5251711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 264360628319) ^ 132180314159 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 264360628319) ^ 10503422 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 264360628319) ^ 50338 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_270190103969 : Nat.Prime 270190103969 := by
  apply lucas_primality 270190103969 (3 : ZMod 270190103969)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (223, 1), (37862963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (223, 1), (37862963, 1)] : List FactorBlock).map factorBlockValue).prod) = 270190103969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_223
      · exact prime_oneHundredThreeCW_37862963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 270190103969) ^ 135095051984 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 270190103969) ^ 1211614816 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 270190103969) ^ 7136 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_286977089527 : Nat.Prime 286977089527 := by
  apply lucas_primality 286977089527 (5 : ZMod 286977089527)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (2079544127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (2079544127, 1)] : List FactorBlock).map factorBlockValue).prod) = 286977089527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_2079544127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 286977089527) ^ 143488544763 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 286977089527) ^ 95659029842 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 286977089527) ^ 12477264762 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 286977089527) ^ 138 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_307389262709 : Nat.Prime 307389262709 := by
  apply lucas_primality 307389262709 (2 : ZMod 307389262709)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (31, 1), (225358697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (31, 1), (225358697, 1)] : List FactorBlock).map factorBlockValue).prod) = 307389262709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_225358697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 307389262709) ^ 153694631354 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 307389262709) ^ 27944478428 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 307389262709) ^ 9915782668 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 307389262709) ^ 1364 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_308766347401 : Nat.Prime 308766347401 := by
  apply lucas_primality 308766347401 (22 : ZMod 308766347401)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (7, 1), (23, 1), (61, 2), (859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (7, 1), (23, 1), (61, 2), (859, 1)] : List FactorBlock).map factorBlockValue).prod) = 308766347401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_61
      · exact prime_oneHundredThreeCW_859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 308766347401) ^ 154383173700 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 308766347401) ^ 102922115800 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 308766347401) ^ 61753269480 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 308766347401) ^ 44109478200 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 308766347401) ^ 13424623800 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 308766347401) ^ 5061743400 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 308766347401) ^ 359448600 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_358870085473 : Nat.Prime 358870085473 := by
  apply lucas_primality 358870085473 (5 : ZMod 358870085473)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (499, 1), (983, 1), (7621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (499, 1), (983, 1), (7621, 1)] : List FactorBlock).map factorBlockValue).prod) = 358870085473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_499
      · exact prime_oneHundredThreeCW_983
      · exact prime_oneHundredThreeCW_7621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 358870085473) ^ 179435042736 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 358870085473) ^ 119623361824 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 358870085473) ^ 719178528 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 358870085473) ^ 365076384 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 358870085473) ^ 47089632 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_469933237751 : Nat.Prime 469933237751 := by
  apply lucas_primality 469933237751 (17 : ZMod 469933237751)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (21269, 1), (88379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (21269, 1), (88379, 1)] : List FactorBlock).map factorBlockValue).prod) = 469933237751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_21269
      · exact prime_oneHundredThreeCW_88379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 469933237751) ^ 234966618875 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 469933237751) ^ 93986647550 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 469933237751) ^ 22094750 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 469933237751) ^ 5317250 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_531056153203 : Nat.Prime 531056153203 := by
  apply lucas_primality 531056153203 (2 : ZMod 531056153203)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (88509358867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (88509358867, 1)] : List FactorBlock).map factorBlockValue).prod) = 531056153203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_88509358867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 531056153203) ^ 265528076601 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 531056153203) ^ 177018717734 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 531056153203) ^ 6 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_615281548379 : Nat.Prime 615281548379 := by
  apply lucas_primality 615281548379 (2 : ZMod 615281548379)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (157, 1), (439, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (157, 1), (439, 1), (13567, 1)] : List FactorBlock).map factorBlockValue).prod) = 615281548379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_47
      · exact prime_oneHundredThreeCW_157
      · exact prime_oneHundredThreeCW_439
      · exact prime_oneHundredThreeCW_13567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 615281548379) ^ 307640774189 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 615281548379) ^ 87897364054 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 615281548379) ^ 13091096774 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 615281548379) ^ 3918990754 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 615281548379) ^ 1401552502 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 615281548379) ^ 45351334 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_689051820887 : Nat.Prime 689051820887 := by
  apply lucas_primality 689051820887 (5 : ZMod 689051820887)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (9221, 1), (261281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (9221, 1), (261281, 1)] : List FactorBlock).map factorBlockValue).prod) = 689051820887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_9221
      · exact prime_oneHundredThreeCW_261281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 689051820887) ^ 344525910443 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 689051820887) ^ 62641074626 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 689051820887) ^ 53003986222 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 689051820887) ^ 74726366 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 689051820887) ^ 2637206 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_693355626427 : Nat.Prime 693355626427 := by
  apply lucas_primality 693355626427 (2 : ZMod 693355626427)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (115559271071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (115559271071, 1)] : List FactorBlock).map factorBlockValue).prod) = 693355626427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_115559271071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 693355626427) ^ 346677813213 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 693355626427) ^ 231118542142 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 693355626427) ^ 6 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_696470408999 : Nat.Prime 696470408999 := by
  apply lucas_primality 696470408999 (7 : ZMod 696470408999)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (139, 1), (27530651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (139, 1), (27530651, 1)] : List FactorBlock).map factorBlockValue).prod) = 696470408999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_139
      · exact prime_oneHundredThreeCW_27530651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 696470408999) ^ 348235204499 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 696470408999) ^ 99495772714 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 696470408999) ^ 53574646846 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 696470408999) ^ 5010578482 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 696470408999) ^ 25298 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1206797014681 : Nat.Prime 1206797014681 := by
  apply lucas_primality 1206797014681 (7 : ZMod 1206797014681)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (443, 1), (22701223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (443, 1), (22701223, 1)] : List FactorBlock).map factorBlockValue).prod) = 1206797014681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_443
      · exact prime_oneHundredThreeCW_22701223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1206797014681) ^ 603398507340 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1206797014681) ^ 402265671560 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1206797014681) ^ 241359402936 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1206797014681) ^ 2724146760 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1206797014681) ^ 53160 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1293308327029 : Nat.Prime 1293308327029 := by
  apply lucas_primality 1293308327029 (7 : ZMod 1293308327029)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (263, 1), (4057, 1), (101009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (263, 1), (4057, 1), (101009, 1)] : List FactorBlock).map factorBlockValue).prod) = 1293308327029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_263
      · exact prime_oneHundredThreeCW_4057
      · exact prime_oneHundredThreeCW_101009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1293308327029) ^ 646654163514 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1293308327029) ^ 431102775676 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1293308327029) ^ 4917522156 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1293308327029) ^ 318784404 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1293308327029) ^ 12803892 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1347017582087 : Nat.Prime 1347017582087 := by
  apply lucas_primality 1347017582087 (5 : ZMod 1347017582087)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (283, 1), (2713, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (283, 1), (2713, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1347017582087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_283
      · exact prime_oneHundredThreeCW_2713
      · exact prime_oneHundredThreeCW_4691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1347017582087) ^ 673508791043 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1347017582087) ^ 122456143826 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1347017582087) ^ 79236328358 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1347017582087) ^ 4759779442 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1347017582087) ^ 496504822 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1347017582087) ^ 287149346 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1393856422667 : Nat.Prime 1393856422667 := by
  apply lucas_primality 1393856422667 (2 : ZMod 1393856422667)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (727, 1), (958635779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (727, 1), (958635779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1393856422667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_727
      · exact prime_oneHundredThreeCW_958635779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1393856422667) ^ 696928211333 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1393856422667) ^ 1917271558 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1393856422667) ^ 1454 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1501394158519 : Nat.Prime 1501394158519 := by
  apply lucas_primality 1501394158519 (6 : ZMod 1501394158519)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (2579715049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (2579715049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1501394158519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_97
      · exact prime_oneHundredThreeCW_2579715049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1501394158519) ^ 750697079259 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1501394158519) ^ 500464719506 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1501394158519) ^ 15478290294 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1501394158519) ^ 582 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1780030912739 : Nat.Prime 1780030912739 := by
  apply lucas_primality 1780030912739 (2 : ZMod 1780030912739)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (73, 1), (937845581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (73, 1), (937845581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1780030912739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_73
      · exact prime_oneHundredThreeCW_937845581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1780030912739) ^ 890015456369 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1780030912739) ^ 136925454826 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1780030912739) ^ 24383985106 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1780030912739) ^ 1898 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2269831599097 : Nat.Prime 2269831599097 := by
  apply lucas_primality 2269831599097 (5 : ZMod 2269831599097)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (94576316629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (94576316629, 1)] : List FactorBlock).map factorBlockValue).prod) = 2269831599097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_94576316629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2269831599097) ^ 1134915799548 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2269831599097) ^ 756610533032 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2269831599097) ^ 24 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2305290961609 : Nat.Prime 2305290961609 := by
  apply lucas_primality 2305290961609 (14 : ZMod 2305290961609)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (47, 1), (65925731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (47, 1), (65925731, 1)] : List FactorBlock).map factorBlockValue).prod) = 2305290961609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_47
      · exact prime_oneHundredThreeCW_65925731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2305290961609) ^ 1152645480804 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 2305290961609) ^ 768430320536 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 2305290961609) ^ 74364224568 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 2305290961609) ^ 49048743864 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 2305290961609) ^ 34968 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2562492705067 : Nat.Prime 2562492705067 := by
  apply lucas_primality 2562492705067 (2 : ZMod 2562492705067)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (20337243691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (20337243691, 1)] : List FactorBlock).map factorBlockValue).prod) = 2562492705067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_20337243691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2562492705067) ^ 1281246352533 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2562492705067) ^ 854164235022 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2562492705067) ^ 366070386438 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2562492705067) ^ 126 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2729196301889 : Nat.Prime 2729196301889 := by
  apply lucas_primality 2729196301889 (3 : ZMod 2729196301889)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 2), (331, 1), (2629243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 2), (331, 1), (2629243, 1)] : List FactorBlock).map factorBlockValue).prod) = 2729196301889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_331
      · exact prime_oneHundredThreeCW_2629243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2729196301889) ^ 1364598150944 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729196301889) ^ 389885185984 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729196301889) ^ 8245306048 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729196301889) ^ 1038016 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2924880709901 : Nat.Prime 2924880709901 := by
  apply lucas_primality 2924880709901 (2 : ZMod 2924880709901)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (41, 1), (713385539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (41, 1), (713385539, 1)] : List FactorBlock).map factorBlockValue).prod) = 2924880709901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_41
      · exact prime_oneHundredThreeCW_713385539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2924880709901) ^ 1462440354950 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2924880709901) ^ 584976141980 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2924880709901) ^ 71338553900 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2924880709901) ^ 4100 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_4214781383789 : Nat.Prime 4214781383789 := by
  apply lucas_primality 4214781383789 (2 : ZMod 4214781383789)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (773, 1), (31700573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (773, 1), (31700573, 1)] : List FactorBlock).map factorBlockValue).prod) = 4214781383789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_43
      · exact prime_oneHundredThreeCW_773
      · exact prime_oneHundredThreeCW_31700573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4214781383789) ^ 2107390691894 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4214781383789) ^ 98018171716 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4214781383789) ^ 5452498556 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4214781383789) ^ 132956 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_4303898311871 : Nat.Prime 4303898311871 := by
  apply lucas_primality 4303898311871 (11 : ZMod 4303898311871)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (102551, 1), (4196837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (102551, 1), (4196837, 1)] : List FactorBlock).map factorBlockValue).prod) = 4303898311871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_102551
      · exact prime_oneHundredThreeCW_4196837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 4303898311871) ^ 2151949155935 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 4303898311871) ^ 860779662374 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 4303898311871) ^ 41968370 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 4303898311871) ^ 1025510 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_4391382787331 : Nat.Prime 4391382787331 := by
  apply lucas_primality 4391382787331 (2 : ZMod 4391382787331)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 2), (518463139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 2), (518463139, 1)] : List FactorBlock).map factorBlockValue).prod) = 4391382787331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_518463139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4391382787331) ^ 2195691393665 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4391382787331) ^ 878276557466 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4391382787331) ^ 627340398190 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4391382787331) ^ 399216617030 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4391382787331) ^ 8470 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_4710741977881 : Nat.Prime 4710741977881 := by
  apply lucas_primality 4710741977881 (19 : ZMod 4710741977881)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (3347, 1), (3909589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (3347, 1), (3909589, 1)] : List FactorBlock).map factorBlockValue).prod) = 4710741977881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_3347
      · exact prime_oneHundredThreeCW_3909589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 4710741977881) ^ 2355370988940 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (19 : ZMod 4710741977881) ^ 1570247325960 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (19 : ZMod 4710741977881) ^ 942148395576 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (19 : ZMod 4710741977881) ^ 1407452040 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (19 : ZMod 4710741977881) ^ 1204920 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_5888709554197 : Nat.Prime 5888709554197 := by
  apply lucas_primality 5888709554197 (2 : ZMod 5888709554197)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (31, 1), (14221, 1), (22717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (31, 1), (14221, 1), (22717, 1)] : List FactorBlock).map factorBlockValue).prod) = 5888709554197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_14221
      · exact prime_oneHundredThreeCW_22717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5888709554197) ^ 2944354777098 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5888709554197) ^ 1962903184732 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5888709554197) ^ 841244222028 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5888709554197) ^ 189958372716 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5888709554197) ^ 414085476 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5888709554197) ^ 259220388 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_6049588740907 : Nat.Prime 6049588740907 := by
  apply lucas_primality 6049588740907 (3 : ZMod 6049588740907)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (271, 1), (3720534281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (271, 1), (3720534281, 1)] : List FactorBlock).map factorBlockValue).prod) = 6049588740907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_271
      · exact prime_oneHundredThreeCW_3720534281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6049588740907) ^ 3024794370453 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6049588740907) ^ 2016529580302 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6049588740907) ^ 22323205686 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6049588740907) ^ 1626 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_6197523099199 : Nat.Prime 6197523099199 := by
  apply lucas_primality 6197523099199 (3 : ZMod 6197523099199)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (58171, 1), (17756623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (58171, 1), (17756623, 1)] : List FactorBlock).map factorBlockValue).prod) = 6197523099199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_58171
      · exact prime_oneHundredThreeCW_17756623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6197523099199) ^ 3098761549599 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6197523099199) ^ 2065841033066 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6197523099199) ^ 106539738 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6197523099199) ^ 349026 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_7010638194811 : Nat.Prime 7010638194811 := by
  apply lucas_primality 7010638194811 (2 : ZMod 7010638194811)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (167, 1), (2543, 1), (550267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (167, 1), (2543, 1), (550267, 1)] : List FactorBlock).map factorBlockValue).prod) = 7010638194811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_167
      · exact prime_oneHundredThreeCW_2543
      · exact prime_oneHundredThreeCW_550267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7010638194811) ^ 3505319097405 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7010638194811) ^ 2336879398270 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7010638194811) ^ 1402127638962 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7010638194811) ^ 41979869430 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7010638194811) ^ 2756837670 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7010638194811) ^ 12740430 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_7104522318679 : Nat.Prime 7104522318679 := by
  apply lucas_primality 7104522318679 (3 : ZMod 7104522318679)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (293, 1), (1347084247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (293, 1), (1347084247, 1)] : List FactorBlock).map factorBlockValue).prod) = 7104522318679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_293
      · exact prime_oneHundredThreeCW_1347084247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7104522318679) ^ 3552261159339 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7104522318679) ^ 2368174106226 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7104522318679) ^ 24247516446 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7104522318679) ^ 5274 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_8172218641711 : Nat.Prime 8172218641711 := by
  apply lucas_primality 8172218641711 (6 : ZMod 8172218641711)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (71, 1), (131, 1), (1722821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (71, 1), (131, 1), (1722821, 1)] : List FactorBlock).map factorBlockValue).prod) = 8172218641711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_71
      · exact prime_oneHundredThreeCW_131
      · exact prime_oneHundredThreeCW_1722821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8172218641711) ^ 4086109320855 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 8172218641711) ^ 2724072880570 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 8172218641711) ^ 1634443728342 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 8172218641711) ^ 480718743630 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 8172218641711) ^ 115101671010 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 8172218641711) ^ 62383348410 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 8172218641711) ^ 4743510 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_8338683201983 : Nat.Prime 8338683201983 := by
  apply lucas_primality 8338683201983 (5 : ZMod 8338683201983)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (97, 1), (6140414729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (97, 1), (6140414729, 1)] : List FactorBlock).map factorBlockValue).prod) = 8338683201983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_97
      · exact prime_oneHundredThreeCW_6140414729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8338683201983) ^ 4169341600991 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8338683201983) ^ 1191240457426 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8338683201983) ^ 85965806206 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8338683201983) ^ 1358 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_9281938015249 : Nat.Prime 9281938015249 := by
  apply lucas_primality 9281938015249 (17 : ZMod 9281938015249)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (30391, 1), (219409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (30391, 1), (219409, 1)] : List FactorBlock).map factorBlockValue).prod) = 9281938015249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_29
      · exact prime_oneHundredThreeCW_30391
      · exact prime_oneHundredThreeCW_219409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 9281938015249) ^ 4640969007624 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 9281938015249) ^ 3093979338416 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 9281938015249) ^ 320066828112 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 9281938015249) ^ 305417328 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 9281938015249) ^ 42304272 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_13297583702927 : Nat.Prime 13297583702927 := by
  apply lucas_primality 13297583702927 (5 : ZMod 13297583702927)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (91079340431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (91079340431, 1)] : List FactorBlock).map factorBlockValue).prod) = 13297583702927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_73
      · exact prime_oneHundredThreeCW_91079340431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 13297583702927) ^ 6648791851463 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 13297583702927) ^ 182158680862 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 13297583702927) ^ 146 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_16788631681949 : Nat.Prime 16788631681949 := by
  apply lucas_primality 16788631681949 (2 : ZMod 16788631681949)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (54011, 1), (11101331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (54011, 1), (11101331, 1)] : List FactorBlock).map factorBlockValue).prod) = 16788631681949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_54011
      · exact prime_oneHundredThreeCW_11101331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16788631681949) ^ 8394315840974 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16788631681949) ^ 2398375954564 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16788631681949) ^ 310837268 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16788631681949) ^ 1512308 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_27981396788537 : Nat.Prime 27981396788537 := by
  apply lucas_primality 27981396788537 (3 : ZMod 27981396788537)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (499, 1), (226108643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (499, 1), (226108643, 1)] : List FactorBlock).map factorBlockValue).prod) = 27981396788537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_499
      · exact prime_oneHundredThreeCW_226108643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 27981396788537) ^ 13990698394268 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 27981396788537) ^ 902625702856 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 27981396788537) ^ 56074943464 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 27981396788537) ^ 123752 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_28264451867287 : Nat.Prime 28264451867287 := by
  apply lucas_primality 28264451867287 (3 : ZMod 28264451867287)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4710741977881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4710741977881, 1)] : List FactorBlock).map factorBlockValue).prod) = 28264451867287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_4710741977881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 28264451867287) ^ 14132225933643 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 28264451867287) ^ 9421483955762 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 28264451867287) ^ 6 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_28418089274717 : Nat.Prime 28418089274717 := by
  apply lucas_primality 28418089274717 (2 : ZMod 28418089274717)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7104522318679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7104522318679, 1)] : List FactorBlock).map factorBlockValue).prod) = 28418089274717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7104522318679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 28418089274717) ^ 14209044637358 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 28418089274717) ^ 4 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_33294728768831 : Nat.Prime 33294728768831 := by
  apply lucas_primality 33294728768831 (29 : ZMod 33294728768831)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (2351, 1), (83305549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (2351, 1), (83305549, 1)] : List FactorBlock).map factorBlockValue).prod) = 33294728768831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_2351
      · exact prime_oneHundredThreeCW_83305549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 33294728768831) ^ 16647364384415 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (29 : ZMod 33294728768831) ^ 6658945753766 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (29 : ZMod 33294728768831) ^ 1958513456990 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (29 : ZMod 33294728768831) ^ 14161943330 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (29 : ZMod 33294728768831) ^ 399670 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_47421722388727 : Nat.Prime 47421722388727 := by
  apply lucas_primality 47421722388727 (5 : ZMod 47421722388727)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (73, 1), (1289, 1), (3999733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (73, 1), (1289, 1), (3999733, 1)] : List FactorBlock).map factorBlockValue).prod) = 47421722388727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_73
      · exact prime_oneHundredThreeCW_1289
      · exact prime_oneHundredThreeCW_3999733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 47421722388727) ^ 23710861194363 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 47421722388727) ^ 15807240796242 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 47421722388727) ^ 6774531769818 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 47421722388727) ^ 649612635462 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 47421722388727) ^ 36789544134 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 47421722388727) ^ 11856222 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_51915559243199 : Nat.Prime 51915559243199 := by
  apply lucas_primality 51915559243199 (7 : ZMod 51915559243199)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (79, 1), (149, 1), (683, 1), (14879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (79, 1), (149, 1), (683, 1), (14879, 1)] : List FactorBlock).map factorBlockValue).prod) = 51915559243199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_79
      · exact prime_oneHundredThreeCW_149
      · exact prime_oneHundredThreeCW_683
      · exact prime_oneHundredThreeCW_14879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 51915559243199) ^ 25957779621599 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 51915559243199) ^ 7416508463314 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 51915559243199) ^ 1674695459458 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 51915559243199) ^ 657158977762 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 51915559243199) ^ 348426572102 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 51915559243199) ^ 76011067706 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 51915559243199) ^ 3489183362 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_60320088965089 : Nat.Prime 60320088965089 := by
  apply lucas_primality 60320088965089 (11 : ZMod 60320088965089)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (209444753351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (209444753351, 1)] : List FactorBlock).map factorBlockValue).prod) = 60320088965089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_209444753351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 60320088965089) ^ 30160044482544 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 60320088965089) ^ 20106696321696 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 60320088965089) ^ 288 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_74324921726243 : Nat.Prime 74324921726243 := by
  apply lucas_primality 74324921726243 (2 : ZMod 74324921726243)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (59, 1), (569, 1), (100634641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (59, 1), (569, 1), (100634641, 1)] : List FactorBlock).map factorBlockValue).prod) = 74324921726243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_59
      · exact prime_oneHundredThreeCW_569
      · exact prime_oneHundredThreeCW_100634641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 74324921726243) ^ 37162460863121 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74324921726243) ^ 6756811066022 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74324921726243) ^ 1259744436038 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74324921726243) ^ 130623764018 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74324921726243) ^ 738562 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_82261917049547 : Nat.Prime 82261917049547 := by
  apply lucas_primality 82261917049547 (2 : ZMod 82261917049547)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (167, 1), (32957, 1), (574859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (167, 1), (32957, 1), (574859, 1)] : List FactorBlock).map factorBlockValue).prod) = 82261917049547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_167
      · exact prime_oneHundredThreeCW_32957
      · exact prime_oneHundredThreeCW_574859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 82261917049547) ^ 41130958524773 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 82261917049547) ^ 6327839773042 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 82261917049547) ^ 492586329638 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 82261917049547) ^ 2496037778 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 82261917049547) ^ 143099294 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_93824272212607 : Nat.Prime 93824272212607 := by
  apply lucas_primality 93824272212607 (3 : ZMod 93824272212607)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (90073, 1), (4451483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (90073, 1), (4451483, 1)] : List FactorBlock).map factorBlockValue).prod) = 93824272212607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_90073
      · exact prime_oneHundredThreeCW_4451483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93824272212607) ^ 46912136106303 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 93824272212607) ^ 31274757404202 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 93824272212607) ^ 7217251708662 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 93824272212607) ^ 1041647022 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 93824272212607) ^ 21077082 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_98330403419603 : Nat.Prime 98330403419603 := by
  apply lucas_primality 98330403419603 (2 : ZMod 98330403419603)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (358870085473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (358870085473, 1)] : List FactorBlock).map factorBlockValue).prod) = 98330403419603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_137
      · exact prime_oneHundredThreeCW_358870085473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 98330403419603) ^ 49165201709801 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 98330403419603) ^ 717740170946 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 98330403419603) ^ 274 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_98458139380609 : Nat.Prime 98458139380609 := by
  apply lucas_primality 98458139380609 (11 : ZMod 98458139380609)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (7, 1), (269, 1), (593, 1), (76541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (7, 1), (269, 1), (593, 1), (76541, 1)] : List FactorBlock).map factorBlockValue).prod) = 98458139380609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_269
      · exact prime_oneHundredThreeCW_593
      · exact prime_oneHundredThreeCW_76541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 98458139380609) ^ 49229069690304 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 98458139380609) ^ 32819379793536 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 98458139380609) ^ 14065448482944 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 98458139380609) ^ 366015388032 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 98458139380609) ^ 166033961856 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 98458139380609) ^ 1286345088 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_137006664798833 : Nat.Prime 137006664798833 := by
  apply lucas_primality 137006664798833 (3 : ZMod 137006664798833)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (270953, 1), (31602959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (270953, 1), (31602959, 1)] : List FactorBlock).map factorBlockValue).prod) = 137006664798833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_270953
      · exact prime_oneHundredThreeCW_31602959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 137006664798833) ^ 68503332399416 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 137006664798833) ^ 505647344 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 137006664798833) ^ 4335248 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_168155260827557 : Nat.Prime 168155260827557 := by
  apply lucas_primality 168155260827557 (2 : ZMod 168155260827557)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (787, 1), (1753, 1), (30471499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (787, 1), (1753, 1), (30471499, 1)] : List FactorBlock).map factorBlockValue).prod) = 168155260827557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_787
      · exact prime_oneHundredThreeCW_1753
      · exact prime_oneHundredThreeCW_30471499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 168155260827557) ^ 84077630413778 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 168155260827557) ^ 213666150988 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 168155260827557) ^ 95924278852 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 168155260827557) ^ 5518444 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_301025181851507 : Nat.Prime 301025181851507 := by
  apply lucas_primality 301025181851507 (2 : ZMod 301025181851507)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (61, 1), (50355500477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (61, 1), (50355500477, 1)] : List FactorBlock).map factorBlockValue).prod) = 301025181851507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_61
      · exact prime_oneHundredThreeCW_50355500477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 301025181851507) ^ 150512590925753 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 301025181851507) ^ 43003597407358 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 301025181851507) ^ 4934839046746 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 301025181851507) ^ 5978 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_346263404496979 : Nat.Prime 346263404496979 := by
  apply lucas_primality 346263404496979 (2 : ZMod 346263404496979)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (79, 1), (23564951987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (79, 1), (23564951987, 1)] : List FactorBlock).map factorBlockValue).prod) = 346263404496979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_79
      · exact prime_oneHundredThreeCW_23564951987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 346263404496979) ^ 173131702248489 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 346263404496979) ^ 115421134832326 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 346263404496979) ^ 11169787241838 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 346263404496979) ^ 4383081069582 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 346263404496979) ^ 14694 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_395986938932681 : Nat.Prime 395986938932681 := by
  apply lucas_primality 395986938932681 (3 : ZMod 395986938932681)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (719, 1), (6737, 1), (2043739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (719, 1), (6737, 1), (2043739, 1)] : List FactorBlock).map factorBlockValue).prod) = 395986938932681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_719
      · exact prime_oneHundredThreeCW_6737
      · exact prime_oneHundredThreeCW_2043739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 395986938932681) ^ 197993469466340 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 395986938932681) ^ 79197387786536 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 395986938932681) ^ 550746785720 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 395986938932681) ^ 58777933640 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 395986938932681) ^ 193756120 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_422188677432043 : Nat.Prime 422188677432043 := by
  apply lucas_primality 422188677432043 (2 : ZMod 422188677432043)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (2269831599097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (2269831599097, 1)] : List FactorBlock).map factorBlockValue).prod) = 422188677432043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_2269831599097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 422188677432043) ^ 211094338716021 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 422188677432043) ^ 140729559144014 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 422188677432043) ^ 13618989594582 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 422188677432043) ^ 186 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_445099652402633 : Nat.Prime 445099652402633 := by
  apply lucas_primality 445099652402633 (3 : ZMod 445099652402633)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (181, 1), (307389262709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (181, 1), (307389262709, 1)] : List FactorBlock).map factorBlockValue).prod) = 445099652402633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_181
      · exact prime_oneHundredThreeCW_307389262709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 445099652402633) ^ 222549826201316 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 445099652402633) ^ 2459114101672 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 445099652402633) ^ 1448 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_743780876268179 : Nat.Prime 743780876268179 := by
  apply lucas_primality 743780876268179 (2 : ZMod 743780876268179)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (45413, 1), (1169867779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (45413, 1), (1169867779, 1)] : List FactorBlock).map factorBlockValue).prod) = 743780876268179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_45413
      · exact prime_oneHundredThreeCW_1169867779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 743780876268179) ^ 371890438134089 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 743780876268179) ^ 106254410895454 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 743780876268179) ^ 16378148906 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 743780876268179) ^ 635782 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_843871834478107 : Nat.Prime 843871834478107 := by
  apply lucas_primality 843871834478107 (2 : ZMod 843871834478107)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (12211, 1), (60941369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (12211, 1), (60941369, 1)] : List FactorBlock).map factorBlockValue).prod) = 843871834478107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_12211
      · exact prime_oneHundredThreeCW_60941369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 843871834478107) ^ 421935917239053 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 843871834478107) ^ 281290611492702 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 843871834478107) ^ 120553119211158 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 843871834478107) ^ 69107512446 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 843871834478107) ^ 13847274 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1126089271124201 : Nat.Prime 1126089271124201 := by
  apply lucas_primality 1126089271124201 (3 : ZMod 1126089271124201)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (191, 1), (5591, 1), (5272541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (191, 1), (5591, 1), (5272541, 1)] : List FactorBlock).map factorBlockValue).prod) = 1126089271124201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_191
      · exact prime_oneHundredThreeCW_5591
      · exact prime_oneHundredThreeCW_5272541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1126089271124201) ^ 563044635562100 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126089271124201) ^ 225217854224840 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126089271124201) ^ 5895755346200 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126089271124201) ^ 201411066200 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1126089271124201) ^ 213576200 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1683981561344437 : Nat.Prime 1683981561344437 := by
  apply lucas_primality 1683981561344437 (2 : ZMod 1683981561344437)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (163, 1), (286977089527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (163, 1), (286977089527, 1)] : List FactorBlock).map factorBlockValue).prod) = 1683981561344437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_163
      · exact prime_oneHundredThreeCW_286977089527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1683981561344437) ^ 841990780672218 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1683981561344437) ^ 561327187114812 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1683981561344437) ^ 10331175222972 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1683981561344437) ^ 5868 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2178169778854231 : Nat.Prime 2178169778854231 := by
  apply lucas_primality 2178169778854231 (6 : ZMod 2178169778854231)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (31063, 1), (333909701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (31063, 1), (333909701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2178169778854231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_31063
      · exact prime_oneHundredThreeCW_333909701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2178169778854231) ^ 1089084889427115 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2178169778854231) ^ 726056592951410 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2178169778854231) ^ 435633955770846 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2178169778854231) ^ 311167111264890 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2178169778854231) ^ 70121037210 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2178169778854231) ^ 6523230 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2408201454812057 : Nat.Prime 2408201454812057 := by
  apply lucas_primality 2408201454812057 (3 : ZMod 2408201454812057)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (301025181851507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (301025181851507, 1)] : List FactorBlock).map factorBlockValue).prod) = 2408201454812057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_301025181851507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2408201454812057) ^ 1204100727406028 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2408201454812057) ^ 8 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2433907251159913 : Nat.Prime 2433907251159913 := by
  apply lucas_primality 2433907251159913 (5 : ZMod 2433907251159913)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (37, 1), (79, 1), (109, 1), (2609, 1), (3697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (37, 1), (79, 1), (109, 1), (2609, 1), (3697, 1)] : List FactorBlock).map factorBlockValue).prod) = 2433907251159913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_37
      · exact prime_oneHundredThreeCW_79
      · exact prime_oneHundredThreeCW_109
      · exact prime_oneHundredThreeCW_2609
      · exact prime_oneHundredThreeCW_3697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2433907251159913) ^ 1216953625579956 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2433907251159913) ^ 811302417053304 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2433907251159913) ^ 221264295559992 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2433907251159913) ^ 65781277058376 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2433907251159913) ^ 30808952546328 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2433907251159913) ^ 22329424322568 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2433907251159913) ^ 932888942568 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2433907251159913) ^ 658346565096 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2843792397755039 : Nat.Prime 2843792397755039 := by
  apply lucas_primality 2843792397755039 (11 : ZMod 2843792397755039)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (185753, 1), (7654768423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (185753, 1), (7654768423, 1)] : List FactorBlock).map factorBlockValue).prod) = 2843792397755039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_185753
      · exact prime_oneHundredThreeCW_7654768423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 2843792397755039) ^ 1421896198877519 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843792397755039) ^ 15309536846 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843792397755039) ^ 371506 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_6256590533653961 : Nat.Prime 6256590533653961 := by
  apply lucas_primality 6256590533653961 (3 : ZMod 6256590533653961)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (227, 1), (689051820887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (227, 1), (689051820887, 1)] : List FactorBlock).map factorBlockValue).prod) = 6256590533653961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_227
      · exact prime_oneHundredThreeCW_689051820887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6256590533653961) ^ 3128295266826980 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6256590533653961) ^ 1251318106730792 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6256590533653961) ^ 27562072835480 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6256590533653961) ^ 9080 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_6788968613718481 : Nat.Prime 6788968613718481 := by
  apply lucas_primality 6788968613718481 (23 : ZMod 6788968613718481)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (7, 1), (1347017582087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (7, 1), (1347017582087, 1)] : List FactorBlock).map factorBlockValue).prod) = 6788968613718481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_1347017582087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 6788968613718481) ^ 3394484306859240 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (23 : ZMod 6788968613718481) ^ 2262989537906160 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (23 : ZMod 6788968613718481) ^ 1357793722743696 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (23 : ZMod 6788968613718481) ^ 969852659102640 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (23 : ZMod 6788968613718481) ^ 5040 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_7064393452445891 : Nat.Prime 7064393452445891 := by
  apply lucas_primality 7064393452445891 (2 : ZMod 7064393452445891)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (3391, 1), (18938884889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (3391, 1), (18938884889, 1)] : List FactorBlock).map factorBlockValue).prod) = 7064393452445891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_3391
      · exact prime_oneHundredThreeCW_18938884889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7064393452445891) ^ 3532196726222945 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7064393452445891) ^ 1412878690489178 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7064393452445891) ^ 642217586585990 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7064393452445891) ^ 2083277337790 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7064393452445891) ^ 373010 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_8468229152236951 : Nat.Prime 8468229152236951 := by
  apply lucas_primality 8468229152236951 (3 : ZMod 8468229152236951)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (8429, 1), (2232564599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (8429, 1), (2232564599, 1)] : List FactorBlock).map factorBlockValue).prod) = 8468229152236951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_8429
      · exact prime_oneHundredThreeCW_2232564599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8468229152236951) ^ 4234114576118475 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8468229152236951) ^ 2822743050745650 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8468229152236951) ^ 1693645830447390 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8468229152236951) ^ 1004654069550 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8468229152236951) ^ 3793050 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_12513181067307923 : Nat.Prime 12513181067307923 := by
  apply lucas_primality 12513181067307923 (2 : ZMod 12513181067307923)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6256590533653961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6256590533653961, 1)] : List FactorBlock).map factorBlockValue).prod) = 12513181067307923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_6256590533653961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 12513181067307923) ^ 6256590533653961 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12513181067307923) ^ 2 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_18860203279645757 : Nat.Prime 18860203279645757 := by
  apply lucas_primality 18860203279645757 (2 : ZMod 18860203279645757)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (131, 1), (177304208623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (131, 1), (177304208623, 1)] : List FactorBlock).map factorBlockValue).prod) = 18860203279645757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_29
      · exact prime_oneHundredThreeCW_131
      · exact prime_oneHundredThreeCW_177304208623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18860203279645757) ^ 9430101639822878 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18860203279645757) ^ 2694314754235108 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18860203279645757) ^ 650351837229164 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18860203279645757) ^ 143971017401876 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18860203279645757) ^ 106372 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_22274177796501017 : Nat.Prime 22274177796501017 := by
  apply lucas_primality 22274177796501017 (3 : ZMod 22274177796501017)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (62761, 1), (2334899753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (62761, 1), (2334899753, 1)] : List FactorBlock).map factorBlockValue).prod) = 22274177796501017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_19
      · exact prime_oneHundredThreeCW_62761
      · exact prime_oneHundredThreeCW_2334899753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22274177796501017) ^ 11137088898250508 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 22274177796501017) ^ 1172325147184264 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 22274177796501017) ^ 354904762456 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 22274177796501017) ^ 9539672 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_30314288700942611 : Nat.Prime 30314288700942611 := by
  apply lucas_primality 30314288700942611 (2 : ZMod 30314288700942611)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 2), (2562492705067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 2), (2562492705067, 1)] : List FactorBlock).map factorBlockValue).prod) = 30314288700942611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_2562492705067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30314288700942611) ^ 15157144350471305 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30314288700942611) ^ 6062857740188522 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30314288700942611) ^ 4330612671563230 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30314288700942611) ^ 2331868361610970 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30314288700942611) ^ 11830 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_42889013944562641 : Nat.Prime 42889013944562641 := by
  apply lucas_primality 42889013944562641 (19 : ZMod 42889013944562641)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (269, 1), (207121, 1), (3207439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (269, 1), (207121, 1), (3207439, 1)] : List FactorBlock).map factorBlockValue).prod) = 42889013944562641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_269
      · exact prime_oneHundredThreeCW_207121
      · exact prime_oneHundredThreeCW_3207439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 42889013944562641) ^ 21444506972281320 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (19 : ZMod 42889013944562641) ^ 14296337981520880 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (19 : ZMod 42889013944562641) ^ 8577802788912528 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (19 : ZMod 42889013944562641) ^ 159438713548560 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (19 : ZMod 42889013944562641) ^ 207072261840 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (19 : ZMod 42889013944562641) ^ 13371731760 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_50555608595593223 : Nat.Prime 50555608595593223 := by
  apply lucas_primality 50555608595593223 (5 : ZMod 50555608595593223)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (173, 1), (883, 1), (46133, 1), (326083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (173, 1), (883, 1), (46133, 1), (326083, 1)] : List FactorBlock).map factorBlockValue).prod) = 50555608595593223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_173
      · exact prime_oneHundredThreeCW_883
      · exact prime_oneHundredThreeCW_46133
      · exact prime_oneHundredThreeCW_326083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 50555608595593223) ^ 25277804297796611 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 50555608595593223) ^ 4595964417781202 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 50555608595593223) ^ 292228951419614 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 50555608595593223) ^ 57254369870434 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 50555608595593223) ^ 1095866485934 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 50555608595593223) ^ 155039080834 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_52363749425769917 : Nat.Prime 52363749425769917 := by
  apply lucas_primality 52363749425769917 (2 : ZMod 52363749425769917)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9582659, 1), (1366106981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9582659, 1), (1366106981, 1)] : List FactorBlock).map factorBlockValue).prod) = 52363749425769917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_9582659
      · exact prime_oneHundredThreeCW_1366106981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52363749425769917) ^ 26181874712884958 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 52363749425769917) ^ 5464427924 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 52363749425769917) ^ 38330636 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_70975246115874931 : Nat.Prime 70975246115874931 := by
  apply lucas_primality 70975246115874931 (3 : ZMod 70975246115874931)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (619, 1), (123291549179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (619, 1), (123291549179, 1)] : List FactorBlock).map factorBlockValue).prod) = 70975246115874931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_619
      · exact prime_oneHundredThreeCW_123291549179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 70975246115874931) ^ 35487623057937465 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 70975246115874931) ^ 23658415371958310 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 70975246115874931) ^ 14195049223174986 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 70975246115874931) ^ 2289524068254030 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 70975246115874931) ^ 114661140736470 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 70975246115874931) ^ 575670 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_147303546333116911 : Nat.Prime 147303546333116911 := by
  apply lucas_primality 147303546333116911 (6 : ZMod 147303546333116911)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (53, 1), (59, 1), (204101, 1), (699401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (53, 1), (59, 1), (204101, 1), (699401, 1)] : List FactorBlock).map factorBlockValue).prod) = 147303546333116911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_53
      · exact prime_oneHundredThreeCW_59
      · exact prime_oneHundredThreeCW_204101
      · exact prime_oneHundredThreeCW_699401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 147303546333116911) ^ 73651773166558455 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 147303546333116911) ^ 49101182111038970 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 147303546333116911) ^ 29460709266623382 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 147303546333116911) ^ 13391231484828810 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 147303546333116911) ^ 2779312194964470 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 147303546333116911) ^ 2496670276832490 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 147303546333116911) ^ 721718885910 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 147303546333116911) ^ 210613862910 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_173517906879605983 : Nat.Prime 173517906879605983 := by
  apply lucas_primality 173517906879605983 (6 : ZMod 173517906879605983)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (29, 1), (83, 1), (269, 1), (3511, 1), (553103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (29, 1), (83, 1), (269, 1), (3511, 1), (553103, 1)] : List FactorBlock).map factorBlockValue).prod) = 173517906879605983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_29
      · exact prime_oneHundredThreeCW_83
      · exact prime_oneHundredThreeCW_269
      · exact prime_oneHundredThreeCW_3511
      · exact prime_oneHundredThreeCW_553103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 173517906879605983) ^ 86758953439802991 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 173517906879605983) ^ 57839302293201994 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 173517906879605983) ^ 7544256820852434 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 173517906879605983) ^ 5983376099296758 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 173517906879605983) ^ 2090577191320554 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 173517906879605983) ^ 645047980965078 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 173517906879605983) ^ 49421220985362 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 173517906879605983) ^ 313717168194 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_224023542514991819 : Nat.Prime 224023542514991819 := by
  apply lucas_primality 224023542514991819 (2 : ZMod 224023542514991819)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23887, 1), (94117, 1), (49823471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23887, 1), (94117, 1), (49823471, 1)] : List FactorBlock).map factorBlockValue).prod) = 224023542514991819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_23887
      · exact prime_oneHundredThreeCW_94117
      · exact prime_oneHundredThreeCW_49823471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 224023542514991819) ^ 112011771257495909 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 224023542514991819) ^ 9378471240214 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 224023542514991819) ^ 2380266503554 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 224023542514991819) ^ 4496345558 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_357303386304920281 : Nat.Prime 357303386304920281 := by
  apply lucas_primality 357303386304920281 (22 : ZMod 357303386304920281)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (71, 1), (251, 1), (20051, 1), (362293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (71, 1), (251, 1), (20051, 1), (362293, 1)] : List FactorBlock).map factorBlockValue).prod) = 357303386304920281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_71
      · exact prime_oneHundredThreeCW_251
      · exact prime_oneHundredThreeCW_20051
      · exact prime_oneHundredThreeCW_362293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 357303386304920281) ^ 178651693152460140 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 357303386304920281) ^ 119101128768306760 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 357303386304920281) ^ 71460677260984056 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 357303386304920281) ^ 15534929839344360 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 357303386304920281) ^ 5032442060632680 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 357303386304920281) ^ 1423519467350280 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 357303386304920281) ^ 17819729006280 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (22 : ZMod 357303386304920281) ^ 986227683960 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_448047085029983639 : Nat.Prime 448047085029983639 := by
  apply lucas_primality 448047085029983639 (7 : ZMod 448047085029983639)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (224023542514991819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (224023542514991819, 1)] : List FactorBlock).map factorBlockValue).prod) = 448047085029983639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_224023542514991819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 448047085029983639) ^ 224023542514991819 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 448047085029983639) ^ 2 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_593716174737781937 : Nat.Prime 593716174737781937 := by
  apply lucas_primality 593716174737781937 (3 : ZMod 593716174737781937)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (236519, 1), (156889133309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (236519, 1), (156889133309, 1)] : List FactorBlock).map factorBlockValue).prod) = 593716174737781937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_236519
      · exact prime_oneHundredThreeCW_156889133309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 593716174737781937) ^ 296858087368890968 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 593716174737781937) ^ 2510226132944 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 593716174737781937) ^ 3784304 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_624775936065270361 : Nat.Prime 624775936065270361 := by
  apply lucas_primality 624775936065270361 (31 : ZMod 624775936065270361)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (743780876268179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (743780876268179, 1)] : List FactorBlock).map factorBlockValue).prod) = 624775936065270361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_743780876268179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 624775936065270361) ^ 312387968032635180 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (31 : ZMod 624775936065270361) ^ 208258645355090120 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (31 : ZMod 624775936065270361) ^ 124955187213054072 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (31 : ZMod 624775936065270361) ^ 89253705152181480 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (31 : ZMod 624775936065270361) ^ 840 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_642657180141501097 : Nat.Prime 642657180141501097 := by
  apply lucas_primality 642657180141501097 (15 : ZMod 642657180141501097)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 1), (19, 1), (23, 1), (3169, 1), (9199, 1), (14699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 1), (19, 1), (23, 1), (3169, 1), (9199, 1), (14699, 1)] : List FactorBlock).map factorBlockValue).prod) = 642657180141501097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_19
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_3169
      · exact prime_oneHundredThreeCW_9199
      · exact prime_oneHundredThreeCW_14699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 642657180141501097) ^ 321328590070750548 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (15 : ZMod 642657180141501097) ^ 214219060047167032 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (15 : ZMod 642657180141501097) ^ 58423380012863736 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (15 : ZMod 642657180141501097) ^ 49435167703192392 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (15 : ZMod 642657180141501097) ^ 33824062112710584 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (15 : ZMod 642657180141501097) ^ 27941616527891352 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (15 : ZMod 642657180141501097) ^ 202794944822184 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (15 : ZMod 642657180141501097) ^ 69861634975704 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (15 : ZMod 642657180141501097) ^ 43721149747704 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_647105952438948391 : Nat.Prime 647105952438948391 := by
  apply lucas_primality 647105952438948391 (6 : ZMod 647105952438948391)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (554597, 1), (38893463929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (554597, 1), (38893463929, 1)] : List FactorBlock).map factorBlockValue).prod) = 647105952438948391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_554597
      · exact prime_oneHundredThreeCW_38893463929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 647105952438948391) ^ 323552976219474195 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 647105952438948391) ^ 215701984146316130 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 647105952438948391) ^ 129421190487789678 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 647105952438948391) ^ 1166803917870 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 647105952438948391) ^ 16637910 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_686224223113002257 : Nat.Prime 686224223113002257 := by
  apply lucas_primality 686224223113002257 (3 : ZMod 686224223113002257)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (42889013944562641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (42889013944562641, 1)] : List FactorBlock).map factorBlockValue).prod) = 686224223113002257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_42889013944562641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 686224223113002257) ^ 343112111556501128 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 686224223113002257) ^ 16 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_686646661224995137 : Nat.Prime 686646661224995137 := by
  apply lucas_primality 686646661224995137 (5 : ZMod 686646661224995137)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (67, 1), (151, 1), (13092318737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (67, 1), (151, 1), (13092318737, 1)] : List FactorBlock).map factorBlockValue).prod) = 686646661224995137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_67
      · exact prime_oneHundredThreeCW_151
      · exact prime_oneHundredThreeCW_13092318737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 686646661224995137) ^ 343323330612497568 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 686646661224995137) ^ 228882220408331712 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 686646661224995137) ^ 10248457630223808 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 686646661224995137) ^ 4547328882284736 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 686646661224995137) ^ 52446528 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_766274219449438823 : Nat.Prime 766274219449438823 := by
  apply lucas_primality 766274219449438823 (5 : ZMod 766274219449438823)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (65063, 1), (5888709554197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (65063, 1), (5888709554197, 1)] : List FactorBlock).map factorBlockValue).prod) = 766274219449438823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_65063
      · exact prime_oneHundredThreeCW_5888709554197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 766274219449438823) ^ 383137109724719411 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 766274219449438823) ^ 11777419108394 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 766274219449438823) ^ 130126 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1607965062390778643 : Nat.Prime 1607965062390778643 := by
  apply lucas_primality 1607965062390778643 (2 : ZMod 1607965062390778643)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (331, 1), (1039, 1), (75412159499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (331, 1), (1039, 1), (75412159499, 1)] : List FactorBlock).map factorBlockValue).prod) = 1607965062390778643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_331
      · exact prime_oneHundredThreeCW_1039
      · exact prime_oneHundredThreeCW_75412159499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1607965062390778643) ^ 803982531195389321 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1607965062390778643) ^ 51869840722283182 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1607965062390778643) ^ 4857900490606582 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1607965062390778643) ^ 1547608337238478 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1607965062390778643) ^ 21322358 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1634442277445115967 : Nat.Prime 1634442277445115967 := by
  apply lucas_primality 1634442277445115967 (3 : ZMod 1634442277445115967)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 2), (181, 1), (997, 1), (15907, 1), (59797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 2), (181, 1), (997, 1), (15907, 1), (59797, 1)] : List FactorBlock).map factorBlockValue).prod) = 1634442277445115967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_181
      · exact prime_oneHundredThreeCW_997
      · exact prime_oneHundredThreeCW_15907
      · exact prime_oneHundredThreeCW_59797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1634442277445115967) ^ 817221138722557983 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1634442277445115967) ^ 544814092481705322 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1634442277445115967) ^ 71062707715005042 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1634442277445115967) ^ 9030067831188486 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1634442277445115967) ^ 1639360358520678 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1634442277445115967) ^ 102749875994538 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1634442277445115967) ^ 27333181889478 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2675578511342088707 : Nat.Prime 2675578511342088707 := by
  apply lucas_primality 2675578511342088707 (2 : ZMod 2675578511342088707)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (4759, 1), (2729196301889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (4759, 1), (2729196301889, 1)] : List FactorBlock).map factorBlockValue).prod) = 2675578511342088707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_103
      · exact prime_oneHundredThreeCW_4759
      · exact prime_oneHundredThreeCW_2729196301889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2675578511342088707) ^ 1337789255671044353 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2675578511342088707) ^ 25976490401379502 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2675578511342088707) ^ 562214438189134 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2675578511342088707) ^ 980354 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_3512423759291137781 : Nat.Prime 3512423759291137781 := by
  apply lucas_primality 3512423759291137781 (2 : ZMod 3512423759291137781)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (281, 1), (13297583702927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (281, 1), (13297583702927, 1)] : List FactorBlock).map factorBlockValue).prod) = 3512423759291137781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_47
      · exact prime_oneHundredThreeCW_281
      · exact prime_oneHundredThreeCW_13297583702927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3512423759291137781) ^ 1756211879645568890 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3512423759291137781) ^ 702484751858227556 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3512423759291137781) ^ 74732420410449740 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3512423759291137781) ^ 12499728680751380 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3512423759291137781) ^ 264140 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_7051778344985375249 : Nat.Prime 7051778344985375249 := by
  apply lucas_primality 7051778344985375249 (3 : ZMod 7051778344985375249)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (1193, 1), (28418089274717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (1193, 1), (28418089274717, 1)] : List FactorBlock).map factorBlockValue).prod) = 7051778344985375249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_1193
      · exact prime_oneHundredThreeCW_28418089274717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7051778344985375249) ^ 3525889172492687624 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7051778344985375249) ^ 542444488075798096 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7051778344985375249) ^ 5910962569141136 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7051778344985375249) ^ 248144 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_15640921168598703557 : Nat.Prime 15640921168598703557 := by
  apply lucas_primality 15640921168598703557 (2 : ZMod 15640921168598703557)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (676661, 1), (186410124179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (676661, 1), (186410124179, 1)] : List FactorBlock).map factorBlockValue).prod) = 15640921168598703557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_676661
      · exact prime_oneHundredThreeCW_186410124179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15640921168598703557) ^ 7820460584299351778 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15640921168598703557) ^ 504545844148345276 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15640921168598703557) ^ 23114855398196 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15640921168598703557) ^ 83905964 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_16072462083831355733 : Nat.Prime 16072462083831355733 := by
  apply lucas_primality 16072462083831355733 (2 : ZMod 16072462083831355733)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (20347, 1), (27541, 1), (7170382579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (20347, 1), (27541, 1), (7170382579, 1)] : List FactorBlock).map factorBlockValue).prod) = 16072462083831355733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_20347
      · exact prime_oneHundredThreeCW_27541
      · exact prime_oneHundredThreeCW_7170382579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16072462083831355733) ^ 8036231041915677866 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16072462083831355733) ^ 789918026432956 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16072462083831355733) ^ 583583097339652 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16072462083831355733) ^ 2241506908 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_20797234032744406121 : Nat.Prime 20797234032744406121 := by
  apply lucas_primality 20797234032744406121 (6 : ZMod 20797234032744406121)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (101, 1), (395986938932681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (101, 1), (395986938932681, 1)] : List FactorBlock).map factorBlockValue).prod) = 20797234032744406121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_101
      · exact prime_oneHundredThreeCW_395986938932681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 20797234032744406121) ^ 10398617016372203060 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 20797234032744406121) ^ 4159446806548881224 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 20797234032744406121) ^ 1599787233288031240 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 20797234032744406121) ^ 205913208244994120 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 20797234032744406121) ^ 52520 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_24852949525907581517 : Nat.Prime 24852949525907581517 := by
  apply lucas_primality 24852949525907581517 (2 : ZMod 24852949525907581517)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1238988809, 1), (5014764731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1238988809, 1), (5014764731, 1)] : List FactorBlock).map factorBlockValue).prod) = 24852949525907581517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_1238988809
      · exact prime_oneHundredThreeCW_5014764731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24852949525907581517) ^ 12426474762953790758 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24852949525907581517) ^ 20059058924 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24852949525907581517) ^ 4955955236 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_29234720457663753239 : Nat.Prime 29234720457663753239 := by
  apply lucas_primality 29234720457663753239 (7 : ZMod 29234720457663753239)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (102547, 1), (6197523099199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (102547, 1), (6197523099199, 1)] : List FactorBlock).map factorBlockValue).prod) = 29234720457663753239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_102547
      · exact prime_oneHundredThreeCW_6197523099199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 29234720457663753239) ^ 14617360228831876619 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 29234720457663753239) ^ 1271074802507119706 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 29234720457663753239) ^ 285086062563154 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 29234720457663753239) ^ 4717162 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_54920251271008935961 : Nat.Prime 54920251271008935961 := by
  apply lucas_primality 54920251271008935961 (11 : ZMod 54920251271008935961)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (56003, 1), (8172218641711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (56003, 1), (8172218641711, 1)] : List FactorBlock).map factorBlockValue).prod) = 54920251271008935961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_56003
      · exact prime_oneHundredThreeCW_8172218641711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 54920251271008935961) ^ 27460125635504467980 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 54920251271008935961) ^ 18306750423669645320 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 54920251271008935961) ^ 10984050254201787192 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 54920251271008935961) ^ 980666237005320 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 54920251271008935961) ^ 6720360 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_72023750237718711269 : Nat.Prime 72023750237718711269 := by
  apply lucas_primality 72023750237718711269 (2 : ZMod 72023750237718711269)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (1549, 1), (5683, 1), (6659, 1), (10592041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (1549, 1), (5683, 1), (6659, 1), (10592041, 1)] : List FactorBlock).map factorBlockValue).prod) = 72023750237718711269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_29
      · exact prime_oneHundredThreeCW_1549
      · exact prime_oneHundredThreeCW_5683
      · exact prime_oneHundredThreeCW_6659
      · exact prime_oneHundredThreeCW_10592041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 72023750237718711269) ^ 36011875118859355634 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 72023750237718711269) ^ 2483577594404093492 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 72023750237718711269) ^ 46496933658953332 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 72023750237718711269) ^ 12673543944697996 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 72023750237718711269) ^ 10816000936735052 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 72023750237718711269) ^ 6799799041348 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_130131377580408022573 : Nat.Prime 130131377580408022573 := by
  apply lucas_primality 130131377580408022573 (2 : ZMod 130131377580408022573)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (37, 1), (43, 1), (241, 1), (283, 1), (857, 1), (8970217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (37, 1), (43, 1), (241, 1), (283, 1), (857, 1), (8970217, 1)] : List FactorBlock).map factorBlockValue).prod) = 130131377580408022573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_37
      · exact prime_oneHundredThreeCW_43
      · exact prime_oneHundredThreeCW_241
      · exact prime_oneHundredThreeCW_283
      · exact prime_oneHundredThreeCW_857
      · exact prime_oneHundredThreeCW_8970217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 130131377580408022573) ^ 65065688790204011286 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 130131377580408022573) ^ 43377125860136007524 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 130131377580408022573) ^ 10010105967723694044 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 130131377580408022573) ^ 3517064258929946556 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 130131377580408022573) ^ 3026311106521116804 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 130131377580408022573) ^ 539964222325344492 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 130131377580408022573) ^ 459828189330063684 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 130131377580408022573) ^ 151845248051817996 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 130131377580408022573) ^ 14507049002316 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_183880324598275148317 : Nat.Prime 183880324598275148317 := by
  apply lucas_primality 183880324598275148317 (2 : ZMod 183880324598275148317)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (1103, 1), (17189, 1), (70481, 1), (1042469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (1103, 1), (17189, 1), (70481, 1), (1042469, 1)] : List FactorBlock).map factorBlockValue).prod) = 183880324598275148317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_1103
      · exact prime_oneHundredThreeCW_17189
      · exact prime_oneHundredThreeCW_70481
      · exact prime_oneHundredThreeCW_1042469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 183880324598275148317) ^ 91940162299137574158 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 183880324598275148317) ^ 61293441532758382772 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 183880324598275148317) ^ 16716393145297740756 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 183880324598275148317) ^ 166709269808046372 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 183880324598275148317) ^ 10697558007928044 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 183880324598275148317) ^ 2608934671731036 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 183880324598275148317) ^ 176389249558764 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_279451562023819383001 : Nat.Prime 279451562023819383001 := by
  apply lucas_primality 279451562023819383001 (14 : ZMod 279451562023819383001)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (11, 1), (8468229152236951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (11, 1), (8468229152236951, 1)] : List FactorBlock).map factorBlockValue).prod) = 279451562023819383001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_8468229152236951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 279451562023819383001) ^ 139725781011909691500 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 279451562023819383001) ^ 93150520674606461000 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 279451562023819383001) ^ 55890312404763876600 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 279451562023819383001) ^ 25404687456710853000 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 279451562023819383001) ^ 33000 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_293276138994231955049 : Nat.Prime 293276138994231955049 := by
  apply lucas_primality 293276138994231955049 (3 : ZMod 293276138994231955049)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (223, 1), (41700017, 1), (3942263491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (223, 1), (41700017, 1), (3942263491, 1)] : List FactorBlock).map factorBlockValue).prod) = 293276138994231955049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_223
      · exact prime_oneHundredThreeCW_41700017
      · exact prime_oneHundredThreeCW_3942263491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 293276138994231955049) ^ 146638069497115977524 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 293276138994231955049) ^ 1315139636745434776 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 293276138994231955049) ^ 7032998067944 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 293276138994231955049) ^ 74392830328 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_295711076119789201741 : Nat.Prime 295711076119789201741 := by
  apply lucas_primality 295711076119789201741 (2 : ZMod 295711076119789201741)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (448047085029983639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (448047085029983639, 1)] : List FactorBlock).map factorBlockValue).prod) = 295711076119789201741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_448047085029983639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 295711076119789201741) ^ 147855538059894600870 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 295711076119789201741) ^ 98570358706596400580 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 295711076119789201741) ^ 59142215223957840348 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 295711076119789201741) ^ 26882825101799018340 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 295711076119789201741) ^ 660 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_309099679687762655819 : Nat.Prime 309099679687762655819 := by
  apply lucas_primality 309099679687762655819 (2 : ZMod 309099679687762655819)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (53, 1), (4231, 1), (98458139380609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (53, 1), (4231, 1), (98458139380609, 1)] : List FactorBlock).map factorBlockValue).prod) = 309099679687762655819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_53
      · exact prime_oneHundredThreeCW_4231
      · exact prime_oneHundredThreeCW_98458139380609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 309099679687762655819) ^ 154549839843881327909 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 309099679687762655819) ^ 44157097098251807974 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 309099679687762655819) ^ 5832069428070993506 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 309099679687762655819) ^ 73055939420411878 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 309099679687762655819) ^ 3139402 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_356828190337043361361 : Nat.Prime 356828190337043361361 := by
  apply lucas_primality 356828190337043361361 (7 : ZMod 356828190337043361361)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (73, 1), (6788968613718481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (73, 1), (6788968613718481, 1)] : List FactorBlock).map factorBlockValue).prod) = 356828190337043361361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_73
      · exact prime_oneHundredThreeCW_6788968613718481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 356828190337043361361) ^ 178414095168521680680 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 356828190337043361361) ^ 118942730112347787120 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 356828190337043361361) ^ 71365638067408672272 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 356828190337043361361) ^ 4888057401877306320 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 356828190337043361361) ^ 52560 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_703192856029708632611 : Nat.Prime 703192856029708632611 := by
  apply lucas_primality 703192856029708632611 (2 : ZMod 703192856029708632611)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (89, 1), (983, 1), (3874711, 1), (18858143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (89, 1), (983, 1), (3874711, 1), (18858143, 1)] : List FactorBlock).map factorBlockValue).prod) = 703192856029708632611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_89
      · exact prime_oneHundredThreeCW_983
      · exact prime_oneHundredThreeCW_3874711
      · exact prime_oneHundredThreeCW_18858143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 703192856029708632611) ^ 351596428014854316305 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 703192856029708632611) ^ 140638571205941726522 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 703192856029708632611) ^ 63926623275428057510 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 703192856029708632611) ^ 7901043326176501490 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 703192856029708632611) ^ 715353871851178670 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 703192856029708632611) ^ 181482659230510 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 703192856029708632611) ^ 37288552538270 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_788433196481412948049 : Nat.Prime 788433196481412948049 := by
  apply lucas_primality 788433196481412948049 (14 : ZMod 788433196481412948049)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (877, 1), (2609, 1), (793327, 1), (822631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (877, 1), (2609, 1), (793327, 1), (822631, 1)] : List FactorBlock).map factorBlockValue).prod) = 788433196481412948049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_877
      · exact prime_oneHundredThreeCW_2609
      · exact prime_oneHundredThreeCW_793327
      · exact prime_oneHundredThreeCW_822631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 788433196481412948049) ^ 394216598240706474024 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 788433196481412948049) ^ 262811065493804316016 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 788433196481412948049) ^ 71675745134673904368 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 788433196481412948049) ^ 899011626546651024 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 788433196481412948049) ^ 302197468946497872 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 788433196481412948049) ^ 993831290856624 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (14 : ZMod 788433196481412948049) ^ 958428744457008 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2287275981055704942859 : Nat.Prime 2287275981055704942859 := by
  apply lucas_primality 2287275981055704942859 (2 : ZMod 2287275981055704942859)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (28260781, 1), (166532169763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (28260781, 1), (166532169763, 1)] : List FactorBlock).map factorBlockValue).prod) = 2287275981055704942859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_28260781
      · exact prime_oneHundredThreeCW_166532169763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2287275981055704942859) ^ 1143637990527852471429 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2287275981055704942859) ^ 762425327018568314286 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2287275981055704942859) ^ 80934634504818 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2287275981055704942859) ^ 13734739566 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_5709251045392693781777 : Nat.Prime 5709251045392693781777 := by
  apply lucas_primality 5709251045392693781777 (3 : ZMod 5709251045392693781777)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (356828190337043361361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (356828190337043361361, 1)] : List FactorBlock).map factorBlockValue).prod) = 5709251045392693781777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_356828190337043361361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5709251045392693781777) ^ 2854625522696346890888 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5709251045392693781777) ^ 16 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_6644754341984946887069 : Nat.Prime 6644754341984946887069 := by
  apply lucas_primality 6644754341984946887069 (2 : ZMod 6644754341984946887069)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (24971, 1), (19750517, 1), (29807537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (24971, 1), (19750517, 1), (29807537, 1)] : List FactorBlock).map factorBlockValue).prod) = 6644754341984946887069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_113
      · exact prime_oneHundredThreeCW_24971
      · exact prime_oneHundredThreeCW_19750517
      · exact prime_oneHundredThreeCW_29807537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6644754341984946887069) ^ 3322377170992473443534 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6644754341984946887069) ^ 58803135769778291036 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6644754341984946887069) ^ 266098848343476308 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6644754341984946887069) ^ 336434450905004 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6644754341984946887069) ^ 222921952323164 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_7483371319357975664633 : Nat.Prime 7483371319357975664633 := by
  apply lucas_primality 7483371319357975664633 (3 : ZMod 7483371319357975664633)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (977, 1), (5165753, 1), (185344245959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (977, 1), (5165753, 1), (185344245959, 1)] : List FactorBlock).map factorBlockValue).prod) = 7483371319357975664633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_977
      · exact prime_oneHundredThreeCW_5165753
      · exact prime_oneHundredThreeCW_185344245959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7483371319357975664633) ^ 3741685659678987832316 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7483371319357975664633) ^ 7659540756763537016 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7483371319357975664633) ^ 1448650626415544 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7483371319357975664633) ^ 40375525448 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_10382522279757407961127 : Nat.Prime 10382522279757407961127 := by
  apply lucas_primality 10382522279757407961127 (3 : ZMod 10382522279757407961127)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (65323, 1), (2408201454812057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (65323, 1), (2408201454812057, 1)] : List FactorBlock).map factorBlockValue).prod) = 10382522279757407961127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_65323
      · exact prime_oneHundredThreeCW_2408201454812057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10382522279757407961127) ^ 5191261139878703980563 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10382522279757407961127) ^ 3460840759919135987042 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10382522279757407961127) ^ 943865661796127996466 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10382522279757407961127) ^ 158941296017595762 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10382522279757407961127) ^ 4311318 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_28558530660924646699721 : Nat.Prime 28558530660924646699721 := by
  apply lucas_primality 28558530660924646699721 (11 : ZMod 28558530660924646699721)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (54920251271008935961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (54920251271008935961, 1)] : List FactorBlock).map factorBlockValue).prod) = 28558530660924646699721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_54920251271008935961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 28558530660924646699721) ^ 14279265330462323349860 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 28558530660924646699721) ^ 5711706132184929339944 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 28558530660924646699721) ^ 2196810050840357438440 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (11 : ZMod 28558530660924646699721) ^ 520 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_33199141722382949798041 : Nat.Prime 33199141722382949798041 := by
  apply lucas_primality 33199141722382949798041 (17 : ZMod 33199141722382949798041)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (421, 1), (62873, 1), (84913, 1), (123090673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (421, 1), (62873, 1), (84913, 1), (123090673, 1)] : List FactorBlock).map factorBlockValue).prod) = 33199141722382949798041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_421
      · exact prime_oneHundredThreeCW_62873
      · exact prime_oneHundredThreeCW_84913
      · exact prime_oneHundredThreeCW_123090673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 33199141722382949798041) ^ 16599570861191474899020 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 33199141722382949798041) ^ 11066380574127649932680 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 33199141722382949798041) ^ 6639828344476589959608 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 33199141722382949798041) ^ 78857818818011757240 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 33199141722382949798041) ^ 528034954947003480 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 33199141722382949798041) ^ 390978315715885080 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (17 : ZMod 33199141722382949798041) ^ 269712894675480 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_54879720125768938866397 : Nat.Prime 54879720125768938866397 := by
  apply lucas_primality 54879720125768938866397 (6 : ZMod 54879720125768938866397)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19, 1), (392110193, 1), (87694199657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19, 1), (392110193, 1), (87694199657, 1)] : List FactorBlock).map factorBlockValue).prod) = 54879720125768938866397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_19
      · exact prime_oneHundredThreeCW_392110193
      · exact prime_oneHundredThreeCW_87694199657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 54879720125768938866397) ^ 27439860062884469433198 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 54879720125768938866397) ^ 18293240041922979622132 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 54879720125768938866397) ^ 7839960017966991266628 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 54879720125768938866397) ^ 2888406322408891519284 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 54879720125768938866397) ^ 139959942652572 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 54879720125768938866397) ^ 625807868028 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_61098144109915663572797 : Nat.Prime 61098144109915663572797 := by
  apply lucas_primality 61098144109915663572797 (2 : ZMod 61098144109915663572797)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (1979, 1), (593716174737781937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (1979, 1), (593716174737781937, 1)] : List FactorBlock).map factorBlockValue).prod) = 61098144109915663572797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_1979
      · exact prime_oneHundredThreeCW_593716174737781937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61098144109915663572797) ^ 30549072054957831786398 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 61098144109915663572797) ^ 4699857239224281813292 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 61098144109915663572797) ^ 30873241086364660724 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 61098144109915663572797) ^ 102908 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_127479470146340930817041 : Nat.Prime 127479470146340930817041 := by
  apply lucas_primality 127479470146340930817041 (3 : ZMod 127479470146340930817041)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (991, 1), (1607965062390778643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (991, 1), (1607965062390778643, 1)] : List FactorBlock).map factorBlockValue).prod) = 127479470146340930817041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_991
      · exact prime_oneHundredThreeCW_1607965062390778643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 127479470146340930817041) ^ 63739735073170465408520 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 127479470146340930817041) ^ 25495894029268186163408 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 127479470146340930817041) ^ 128637204991262291440 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 127479470146340930817041) ^ 79280 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_164973878952974526109847 : Nat.Prime 164973878952974526109847 := by
  apply lucas_primality 164973878952974526109847 (5 : ZMod 164973878952974526109847)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3319, 1), (24852949525907581517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3319, 1), (24852949525907581517, 1)] : List FactorBlock).map factorBlockValue).prod) = 164973878952974526109847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3319
      · exact prime_oneHundredThreeCW_24852949525907581517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 164973878952974526109847) ^ 82486939476487263054923 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 164973878952974526109847) ^ 49705899051815163034 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 164973878952974526109847) ^ 6638 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_239467882219455221268257 : Nat.Prime 239467882219455221268257 := by
  apply lucas_primality 239467882219455221268257 (3 : ZMod 239467882219455221268257)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7483371319357975664633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7483371319357975664633, 1)] : List FactorBlock).map factorBlockValue).prod) = 239467882219455221268257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7483371319357975664633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 239467882219455221268257) ^ 119733941109727610634128 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 239467882219455221268257) ^ 32 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1536632163521530288259117 : Nat.Prime 1536632163521530288259117 := by
  apply lucas_primality 1536632163521530288259117 (2 : ZMod 1536632163521530288259117)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (54879720125768938866397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (54879720125768938866397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1536632163521530288259117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_54879720125768938866397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1536632163521530288259117) ^ 768316081760765144129558 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1536632163521530288259117) ^ 219518880503075755465588 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1536632163521530288259117) ^ 28 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_3054493417176880897827031 : Nat.Prime 3054493417176880897827031 := by
  apply lucas_primality 3054493417176880897827031 (12 : ZMod 3054493417176880897827031)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4571053, 1), (22274177796501017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4571053, 1), (22274177796501017, 1)] : List FactorBlock).map factorBlockValue).prod) = 3054493417176880897827031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_4571053
      · exact prime_oneHundredThreeCW_22274177796501017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 3054493417176880897827031) ^ 1527246708588440448913515 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (12 : ZMod 3054493417176880897827031) ^ 1018164472392293632609010 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (12 : ZMod 3054493417176880897827031) ^ 610898683435376179565406 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (12 : ZMod 3054493417176880897827031) ^ 668225333895030510 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (12 : ZMod 3054493417176880897827031) ^ 137131590 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_3641878429960544030674709 : Nat.Prime 3641878429960544030674709 := by
  apply lucas_primality 3641878429960544030674709 (2 : ZMod 3641878429960544030674709)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (173, 1), (2897, 1), (6723593, 1), (270190103969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (173, 1), (2897, 1), (6723593, 1), (270190103969, 1)] : List FactorBlock).map factorBlockValue).prod) = 3641878429960544030674709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_173
      · exact prime_oneHundredThreeCW_2897
      · exact prime_oneHundredThreeCW_6723593
      · exact prime_oneHundredThreeCW_270190103969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3641878429960544030674709) ^ 1820939214980272015337354 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641878429960544030674709) ^ 21051320404396208269796 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641878429960544030674709) ^ 1257120617866946506964 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641878429960544030674709) ^ 541656585989149556 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641878429960544030674709) ^ 13478948253332 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_4577262406502432369330561 : Nat.Prime 4577262406502432369330561 := by
  apply lucas_primality 4577262406502432369330561 (3 : ZMod 4577262406502432369330561)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (17, 1), (29, 1), (5563, 1), (14983, 1), (18269, 1), (9527003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (17, 1), (29, 1), (5563, 1), (14983, 1), (18269, 1), (9527003, 1)] : List FactorBlock).map factorBlockValue).prod) = 4577262406502432369330561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_29
      · exact prime_oneHundredThreeCW_5563
      · exact prime_oneHundredThreeCW_14983
      · exact prime_oneHundredThreeCW_18269
      · exact prime_oneHundredThreeCW_9527003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4577262406502432369330561) ^ 2288631203251216184665280 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4577262406502432369330561) ^ 915452481300486473866112 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4577262406502432369330561) ^ 269250729794260727607680 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4577262406502432369330561) ^ 157836634706980426528640 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4577262406502432369330561) ^ 822804674906063701120 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4577262406502432369330561) ^ 305497057098206792320 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4577262406502432369330561) ^ 250548054436610234240 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4577262406502432369330561) ^ 480451450104763520 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_33704259358591395171234499 : Nat.Prime 33704259358591395171234499 := by
  apply lucas_primality 33704259358591395171234499 (10 : ZMod 33704259358591395171234499)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (115163, 1), (352619, 1), (1017847, 1), (3160559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (115163, 1), (352619, 1), (1017847, 1), (3160559, 1)] : List FactorBlock).map factorBlockValue).prod) = 33704259358591395171234499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_43
      · exact prime_oneHundredThreeCW_115163
      · exact prime_oneHundredThreeCW_352619
      · exact prime_oneHundredThreeCW_1017847
      · exact prime_oneHundredThreeCW_3160559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 33704259358591395171234499) ^ 16852129679295697585617249 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (10 : ZMod 33704259358591395171234499) ^ 11234753119530465057078166 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (10 : ZMod 33704259358591395171234499) ^ 783819985083520817935686 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (10 : ZMod 33704259358591395171234499) ^ 292665694351409699046 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (10 : ZMod 33704259358591395171234499) ^ 95582652547342585542 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (10 : ZMod 33704259358591395171234499) ^ 33113286533822269134 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (10 : ZMod 33704259358591395171234499) ^ 10664018408955945822 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_67501934070172234342389271 : Nat.Prime 67501934070172234342389271 := by
  apply lucas_primality 67501934070172234342389271 (3 : ZMod 67501934070172234342389271)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (43, 1), (118411, 1), (147303546333116911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (43, 1), (118411, 1), (147303546333116911, 1)] : List FactorBlock).map factorBlockValue).prod) = 67501934070172234342389271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_43
      · exact prime_oneHundredThreeCW_118411
      · exact prime_oneHundredThreeCW_147303546333116911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67501934070172234342389271) ^ 33750967035086117171194635 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 67501934070172234342389271) ^ 22500644690057411447463090 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 67501934070172234342389271) ^ 13500386814034446868477854 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 67501934070172234342389271) ^ 1569812420236563589357890 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 67501934070172234342389271) ^ 570064724309162445570 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 67501934070172234342389271) ^ 458250570 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_174211000089543219962332253 : Nat.Prime 174211000089543219962332253 := by
  apply lucas_primality 174211000089543219962332253 (2 : ZMod 174211000089543219962332253)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (6311, 1), (67103107, 1), (6049588740907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (6311, 1), (67103107, 1), (6049588740907, 1)] : List FactorBlock).map factorBlockValue).prod) = 174211000089543219962332253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_6311
      · exact prime_oneHundredThreeCW_67103107
      · exact prime_oneHundredThreeCW_6049588740907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 174211000089543219962332253) ^ 87105500044771609981166126 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 174211000089543219962332253) ^ 10247705887620189409548956 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 174211000089543219962332253) ^ 27604341639921283467332 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 174211000089543219962332253) ^ 2596168908982757236 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 174211000089543219962332253) ^ 28797164162836 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_178553503024326555357287749 : Nat.Prime 178553503024326555357287749 := by
  apply lucas_primality 178553503024326555357287749 (2 : ZMod 178553503024326555357287749)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (2683, 1), (72023750237718711269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (2683, 1), (72023750237718711269, 1)] : List FactorBlock).map factorBlockValue).prod) = 178553503024326555357287749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_11
      · exact prime_oneHundredThreeCW_2683
      · exact prime_oneHundredThreeCW_72023750237718711269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178553503024326555357287749) ^ 89276751512163277678643874 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 178553503024326555357287749) ^ 59517834341442185119095916 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 178553503024326555357287749) ^ 25507643289189507908183964 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 178553503024326555357287749) ^ 16232136638575141396117068 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 178553503024326555357287749) ^ 66549945219652089212556 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 178553503024326555357287749) ^ 2479092 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_499071676486027503088812479 : Nat.Prime 499071676486027503088812479 := by
  apply lucas_primality 499071676486027503088812479 (7 : ZMod 499071676486027503088812479)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (31, 1), (181, 1), (389, 1), (9629, 1), (1175767, 1), (776778599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (31, 1), (181, 1), (389, 1), (9629, 1), (1175767, 1), (776778599, 1)] : List FactorBlock).map factorBlockValue).prod) = 499071676486027503088812479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_181
      · exact prime_oneHundredThreeCW_389
      · exact prime_oneHundredThreeCW_9629
      · exact prime_oneHundredThreeCW_1175767
      · exact prime_oneHundredThreeCW_776778599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 499071676486027503088812479) ^ 249535838243013751544406239 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 499071676486027503088812479) ^ 38390128960463654083754806 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 499071676486027503088812479) ^ 16099086338258951712542338 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 499071676486027503088812479) ^ 2757302080033301122037638 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 499071676486027503088812479) ^ 1282960607933232655755302 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 499071676486027503088812479) ^ 51830062985359591140182 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 499071676486027503088812479) ^ 424464776172513349234 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 499071676486027503088812479) ^ 642488962914936722 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_738021145833883095476789363 : Nat.Prime 738021145833883095476789363 := by
  apply lucas_primality 738021145833883095476789363 (2 : ZMod 738021145833883095476789363)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31327, 1), (388573, 1), (30314288700942611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31327, 1), (388573, 1), (30314288700942611, 1)] : List FactorBlock).map factorBlockValue).prod) = 738021145833883095476789363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_31327
      · exact prime_oneHundredThreeCW_388573
      · exact prime_oneHundredThreeCW_30314288700942611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 738021145833883095476789363) ^ 369010572916941547738394681 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 738021145833883095476789363) ^ 23558628206782746368206 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 738021145833883095476789363) ^ 1899311444268858349594 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 738021145833883095476789363) ^ 24345652742 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_974187912500725686029361959 : Nat.Prime 974187912500725686029361959 := by
  apply lucas_primality 974187912500725686029361959 (13 : ZMod 974187912500725686029361959)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (692689, 1), (703192856029708632611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (692689, 1), (703192856029708632611, 1)] : List FactorBlock).map factorBlockValue).prod) = 974187912500725686029361959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_692689
      · exact prime_oneHundredThreeCW_703192856029708632611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 974187912500725686029361959) ^ 487093956250362843014680979 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (13 : ZMod 974187912500725686029361959) ^ 1406385712059417265222 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (13 : ZMod 974187912500725686029361959) ^ 1385378 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1268473844401986570350731717 : Nat.Prime 1268473844401986570350731717 := by
  apply lucas_primality 1268473844401986570350731717 (5 : ZMod 1268473844401986570350731717)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (2203, 1), (11953978237, 1), (308766347401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (2203, 1), (11953978237, 1), (308766347401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1268473844401986570350731717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_13
      · exact prime_oneHundredThreeCW_2203
      · exact prime_oneHundredThreeCW_11953978237
      · exact prime_oneHundredThreeCW_308766347401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1268473844401986570350731717) ^ 634236922200993285175365858 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1268473844401986570350731717) ^ 422824614800662190116910572 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1268473844401986570350731717) ^ 97574911107845120796210132 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1268473844401986570350731717) ^ 575793846755327539877772 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1268473844401986570350731717) ^ 106113113078606868 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1268473844401986570350731717) ^ 4108199792753316 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1338170209479018799490881811 : Nat.Prime 1338170209479018799490881811 := by
  apply lucas_primality 1338170209479018799490881811 (2 : ZMod 1338170209479018799490881811)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (438203, 1), (16072462083831355733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (438203, 1), (16072462083831355733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1338170209479018799490881811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_19
      · exact prime_oneHundredThreeCW_438203
      · exact prime_oneHundredThreeCW_16072462083831355733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1338170209479018799490881811) ^ 669085104739509399745440905 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1338170209479018799490881811) ^ 267634041895803759898176362 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1338170209479018799490881811) ^ 70430011025211515762677990 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1338170209479018799490881811) ^ 3053767795927957589270 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1338170209479018799490881811) ^ 83258570 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_1790786603861628099318680071 : Nat.Prime 1790786603861628099318680071 := by
  apply lucas_primality 1790786603861628099318680071 (6 : ZMod 1790786603861628099318680071)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (977, 1), (61098144109915663572797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (977, 1), (61098144109915663572797, 1)] : List FactorBlock).map factorBlockValue).prod) = 1790786603861628099318680071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_977
      · exact prime_oneHundredThreeCW_61098144109915663572797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1790786603861628099318680071) ^ 895393301930814049659340035 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1790786603861628099318680071) ^ 596928867953876033106226690 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1790786603861628099318680071) ^ 358157320772325619863736014 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1790786603861628099318680071) ^ 1832944323297469907183910 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1790786603861628099318680071) ^ 29310 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_2706077534724238016748227663 : Nat.Prime 2706077534724238016748227663 := by
  apply lucas_primality 2706077534724238016748227663 (5 : ZMod 2706077534724238016748227663)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (95400047, 1), (139621541, 1), (101580237653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (95400047, 1), (139621541, 1), (101580237653, 1)] : List FactorBlock).map factorBlockValue).prod) = 2706077534724238016748227663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_95400047
      · exact prime_oneHundredThreeCW_139621541
      · exact prime_oneHundredThreeCW_101580237653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2706077534724238016748227663) ^ 1353038767362119008374113831 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2706077534724238016748227663) ^ 28365578632516166546 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2706077534724238016748227663) ^ 19381518892734739382 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2706077534724238016748227663) ^ 26639803147224854 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_6765193836810595041870569161 : Nat.Prime 6765193836810595041870569161 := by
  apply lucas_primality 6765193836810595041870569161 (7 : ZMod 6765193836810595041870569161)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 2), (31, 1), (4073851, 1), (843871834478107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 2), (31, 1), (4073851, 1), (843871834478107, 1)] : List FactorBlock).map factorBlockValue).prod) = 6765193836810595041870569161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_5
      · exact prime_oneHundredThreeCW_23
      · exact prime_oneHundredThreeCW_31
      · exact prime_oneHundredThreeCW_4073851
      · exact prime_oneHundredThreeCW_843871834478107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6765193836810595041870569161) ^ 3382596918405297520935284580 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6765193836810595041870569161) ^ 2255064612270198347290189720 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6765193836810595041870569161) ^ 1353038767362119008374113832 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6765193836810595041870569161) ^ 294138862470025871385676920 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6765193836810595041870569161) ^ 218232059251954678770018360 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6765193836810595041870569161) ^ 1660638505632777203160 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6765193836810595041870569161) ^ 8016849905880 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_8698106361613622196690731773 : Nat.Prime 8698106361613622196690731773 := by
  apply lucas_primality 8698106361613622196690731773 (2 : ZMod 8698106361613622196690731773)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (143477856971, 1), (1683981561344437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (143477856971, 1), (1683981561344437, 1)] : List FactorBlock).map factorBlockValue).prod) = 8698106361613622196690731773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_143477856971
      · exact prime_oneHundredThreeCW_1683981561344437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8698106361613622196690731773) ^ 4349053180806811098345365886 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8698106361613622196690731773) ^ 2899368787204540732230243924 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8698106361613622196690731773) ^ 60623336208399732 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8698106361613622196690731773) ^ 5165202850956 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_9367191466353131596436172679 : Nat.Prime 9367191466353131596436172679 := by
  apply lucas_primality 9367191466353131596436172679 (3 : ZMod 9367191466353131596436172679)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (197, 1), (881, 1), (2749, 1), (29871473, 1), (109543000817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (197, 1), (881, 1), (2749, 1), (29871473, 1), (109543000817, 1)] : List FactorBlock).map factorBlockValue).prod) = 9367191466353131596436172679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_197
      · exact prime_oneHundredThreeCW_881
      · exact prime_oneHundredThreeCW_2749
      · exact prime_oneHundredThreeCW_29871473
      · exact prime_oneHundredThreeCW_109543000817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9367191466353131596436172679) ^ 4683595733176565798218086339 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 9367191466353131596436172679) ^ 3122397155451043865478724226 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 9367191466353131596436172679) ^ 47549195260675794905767374 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 9367191466353131596436172679) ^ 10632453423783350279723238 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 9367191466353131596436172679) ^ 3407490529775602617837822 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 9367191466353131596436172679) ^ 313583179053578362086 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 9367191466353131596436172679) ^ 85511547031669734 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_20295581510431785125611707473 : Nat.Prime 20295581510431785125611707473 := by
  apply lucas_primality 20295581510431785125611707473 (3 : ZMod 20295581510431785125611707473)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1268473844401986570350731717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1268473844401986570350731717, 1)] : List FactorBlock).map factorBlockValue).prod) = 20295581510431785125611707473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_1268473844401986570350731717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 20295581510431785125611707473) ^ 10147790755215892562805853736 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 20295581510431785125611707473) ^ 16 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_30443372265647677688417561203 : Nat.Prime 30443372265647677688417561203 := by
  apply lucas_primality 30443372265647677688417561203 (2 : ZMod 30443372265647677688417561203)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (143477856971, 1), (1683981561344437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (143477856971, 1), (1683981561344437, 1)] : List FactorBlock).map factorBlockValue).prod) = 30443372265647677688417561203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_7
      · exact prime_oneHundredThreeCW_143477856971
      · exact prime_oneHundredThreeCW_1683981561344437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30443372265647677688417561203) ^ 15221686132823838844208780601 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30443372265647677688417561203) ^ 10147790755215892562805853734 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30443372265647677688417561203) ^ 4349053180806811098345365886 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30443372265647677688417561203) ^ 212181676729399062 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30443372265647677688417561203) ^ 18078209978346 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_121773489062590710753670244803 : Nat.Prime 121773489062590710753670244803 := by
  apply lucas_primality 121773489062590710753670244803 (7 : ZMod 121773489062590710753670244803)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (1579, 1), (5197249177, 1), (60320088965089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (1579, 1), (5197249177, 1), (60320088965089, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_3
      · exact prime_oneHundredThreeCW_41
      · exact prime_oneHundredThreeCW_1579
      · exact prime_oneHundredThreeCW_5197249177
      · exact prime_oneHundredThreeCW_60320088965089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 121773489062590710753670244803) ^ 60886744531295355376835122401 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 121773489062590710753670244803) ^ 40591163020863570251223414934 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 121773489062590710753670244803) ^ 2970085099087578311065127922 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 121773489062590710753670244803) ^ 77120639051672394397511238 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 121773489062590710753670244803) ^ 23430373437065380626 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (7 : ZMod 121773489062590710753670244803) ^ 2018788286818818 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem prime_oneHundredThreeCW_121773489062590710753670244897 : Nat.Prime 121773489062590710753670244897 := by
  apply lucas_primality 121773489062590710753670244897 (3 : ZMod 121773489062590710753670244897)
  · rw [← oneHundredThreeCWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (34141, 1), (196925579, 1), (33294728768831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (34141, 1), (196925579, 1), (33294728768831, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThreeCW_2
      · exact prime_oneHundredThreeCW_17
      · exact prime_oneHundredThreeCW_34141
      · exact prime_oneHundredThreeCW_196925579
      · exact prime_oneHundredThreeCW_33294728768831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 121773489062590710753670244897) ^ 60886744531295355376835122448 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 121773489062590710753670244897) ^ 7163146415446512397274720288 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 121773489062590710753670244897) ^ 3566781554804800994513056 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 121773489062590710753670244897) ^ 618373142183782589024 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide
    · change (3 : ZMod 121773489062590710753670244897) ^ 3657440488795616 ≠ 1
      rw [← oneHundredThreeCWFastPow_eq_pow]
      decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244800 : Nat.totient 121773489062590710753670244800 = 47571291084209273165301350400 := by
  rw [← show ((([(2, 6), (5, 2), (43, 1), (8941, 1), (7074713, 1), (27981396788537, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_43, prime_oneHundredThreeCW_8941, prime_oneHundredThreeCW_7074713, prime_oneHundredThreeCW_27981396788537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244801 : Nat.totient 121773489062590710753670244801 = 96348255082489353563343490320 := by
  rw [← show ((([(7, 1), (13, 1), (1338170209479018799490881811, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_13, prime_oneHundredThreeCW_1338170209479018799490881811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244802 : Nat.totient 121773489062590710753670244802 = 39576054764267149968887685120 := by
  rw [← show ((([(2, 1), (3, 1), (41, 1), (1579, 1), (5197249177, 1), (60320088965089, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_41, prime_oneHundredThreeCW_1579, prime_oneHundredThreeCW_5197249177, prime_oneHundredThreeCW_60320088965089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244803 : Nat.totient 121773489062590710753670244803 = 121773489062590710753670244802 := by
  rw [← show ((([(121773489062590710753670244803, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_121773489062590710753670244803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244804 : Nat.totient 121773489062590710753670244804 = 58716015433670410279611248640 := by
  rw [← show ((([(2, 2), (29, 1), (1193, 1), (2797, 1), (125621, 1), (132947, 1), (18837404447, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_29, prime_oneHundredThreeCW_1193, prime_oneHundredThreeCW_2797, prime_oneHundredThreeCW_125621, prime_oneHundredThreeCW_132947, prime_oneHundredThreeCW_18837404447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244805 : Nat.totient 121773489062590710753670244805 = 59822970899067611090101223424 := by
  rw [← show ((([(3, 1), (5, 1), (19, 1), (37, 1), (1433, 1), (47923609, 1), (168155260827557, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_19, prime_oneHundredThreeCW_37, prime_oneHundredThreeCW_1433, prime_oneHundredThreeCW_47923609, prime_oneHundredThreeCW_168155260827557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244806 : Nat.totient 121773489062590710753670244806 = 59577019641030375257339716416 := by
  rw [← show ((([(2, 1), (73, 1), (127, 1), (21247, 1), (309099679687762655819, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_73, prime_oneHundredThreeCW_127, prime_oneHundredThreeCW_21247, prime_oneHundredThreeCW_309099679687762655819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244807 : Nat.totient 121773489062590710753670244807 = 110702689385570878748289535200 := by
  rw [← show ((([(11, 1), (229549, 1), (490452371, 1), (98330403419603, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_11, prime_oneHundredThreeCW_229549, prime_oneHundredThreeCW_490452371, prime_oneHundredThreeCW_98330403419603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244808 : Nat.totient 121773489062590710753670244808 = 34792425446211974781117924480 := by
  rw [← show ((([(2, 3), (3, 2), (7, 1), (143477856971, 1), (1683981561344437, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_143477856971, prime_oneHundredThreeCW_1683981561344437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244809 : Nat.totient 121773489062590710753670244809 = 120963187911966004251241344000 := by
  rw [← show ((([(151, 1), (31391, 1), (187511953, 1), (137006664798833, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_151, prime_oneHundredThreeCW_31391, prime_oneHundredThreeCW_187511953, prime_oneHundredThreeCW_137006664798833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244810 : Nat.totient 121773489062590710753670244810 = 48361784196066928515667200000 := by
  rw [← show ((([(2, 1), (5, 1), (263, 1), (311, 1), (7753, 1), (394787, 1), (3557501, 1), (13672847, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_263, prime_oneHundredThreeCW_311, prime_oneHundredThreeCW_7753, prime_oneHundredThreeCW_394787, prime_oneHundredThreeCW_3557501, prime_oneHundredThreeCW_13672847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244811 : Nat.totient 121773489062590710753670244811 = 70490542450033711519985602560 := by
  rw [← show ((([(3, 1), (17, 1), (23, 1), (53, 1), (59, 1), (33199141722382949798041, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_17, prime_oneHundredThreeCW_23, prime_oneHundredThreeCW_53, prime_oneHundredThreeCW_59, prime_oneHundredThreeCW_33199141722382949798041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244812 : Nat.totient 121773489062590710753670244812 = 60886744531295355376835122404 := by
  rw [← show ((([(2, 2), (30443372265647677688417561203, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_30443372265647677688417561203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244813 : Nat.totient 121773489062590710753670244813 = 121057838773650154585117555200 := by
  rw [← show ((([(181, 1), (2837, 1), (663709, 1), (357303386304920281, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_181, prime_oneHundredThreeCW_2837, prime_oneHundredThreeCW_663709, prime_oneHundredThreeCW_357303386304920281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244814 : Nat.totient 121773489062590710753670244814 = 37222708529603925956737105920 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (197, 1), (881, 1), (2749, 1), (29871473, 1), (109543000817, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_13, prime_oneHundredThreeCW_197, prime_oneHundredThreeCW_881, prime_oneHundredThreeCW_2749, prime_oneHundredThreeCW_29871473, prime_oneHundredThreeCW_109543000817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244815 : Nat.totient 121773489062590710753670244815 = 82132938758723927772819738240 := by
  rw [← show ((([(5, 1), (7, 1), (61, 1), (693355626427, 1), (82261917049547, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_61, prime_oneHundredThreeCW_693355626427, prime_oneHundredThreeCW_82261917049547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244816 : Nat.totient 121773489062590710753670244816 = 60418686807112705366472985600 := by
  rw [← show ((([(2, 4), (179, 1), (541, 1), (3779, 1), (20797234032744406121, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_179, prime_oneHundredThreeCW_541, prime_oneHundredThreeCW_3779, prime_oneHundredThreeCW_20797234032744406121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244817 : Nat.totient 121773489062590710753670244817 = 81124297157566259684384821920 := by
  rw [← show ((([(3, 2), (1399, 1), (1369044757, 1), (7064393452445891, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_1399, prime_oneHundredThreeCW_1369044757, prime_oneHundredThreeCW_7064393452445891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244818 : Nat.totient 121773489062590710753670244818 = 53566050907297966607186324400 := by
  rw [← show ((([(2, 1), (11, 1), (31, 1), (178553503024326555357287749, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_11, prime_oneHundredThreeCW_31, prime_oneHundredThreeCW_178553503024326555357287749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244819 : Nat.totient 121773489062590710753670244819 = 121736236362636841344576144000 := by
  rw [← show ((([(3331, 1), (176531, 1), (22310971, 1), (9281938015249, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3331, prime_oneHundredThreeCW_176531, prime_oneHundredThreeCW_22310971, prime_oneHundredThreeCW_9281938015249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244820 : Nat.totient 121773489062590710753670244820 = 32472930413914569503760487296 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (11696534309, 1), (173517906879605983, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_11696534309, prime_oneHundredThreeCW_173517906879605983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244821 : Nat.totient 121773489062590710753670244821 = 121708330604172987078498752448 := by
  rw [← show ((([(2039, 1), (22469, 1), (6295717, 1), (422188677432043, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2039, prime_oneHundredThreeCW_22469, prime_oneHundredThreeCW_6295717, prime_oneHundredThreeCW_422188677432043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244822 : Nat.totient 121773489062590710753670244822 = 52188638169681733180144390632 := by
  rw [← show ((([(2, 1), (7, 1), (8698106361613622196690731773, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_8698106361613622196690731773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244823 : Nat.totient 121773489062590710753670244823 = 78590203363672227789486080000 := by
  rw [← show ((([(3, 1), (47, 1), (101, 1), (1361, 1), (7247, 1), (8423, 1), (450503, 1), (228471161, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_47, prime_oneHundredThreeCW_101, prime_oneHundredThreeCW_1361, prime_oneHundredThreeCW_7247, prime_oneHundredThreeCW_8423, prime_oneHundredThreeCW_450503, prime_oneHundredThreeCW_228471161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244824 : Nat.totient 121773489062590710753670244824 = 57682178983056602744890296480 := by
  rw [← show ((([(2, 3), (19, 1), (1238037407, 1), (647105952438948391, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_19, prime_oneHundredThreeCW_1238037407, prime_oneHundredThreeCW_647105952438948391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244825 : Nat.totient 121773489062590710753670244825 = 97418791250069653806307079760 := by
  rw [← show ((([(5, 2), (51915559243199, 1), (93824272212607, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_51915559243199, prime_oneHundredThreeCW_93824272212607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244826 : Nat.totient 121773489062590710753670244826 = 40568484105406913182894080000 := by
  rw [← show ((([(2, 1), (3, 4), (1801, 1), (480541, 1), (719713, 1), (1206797014681, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_1801, prime_oneHundredThreeCW_480541, prime_oneHundredThreeCW_719713, prime_oneHundredThreeCW_1206797014681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244827 : Nat.totient 121773489062590710753670244827 = 112406297596237579157234072136 := by
  rw [← show ((([(13, 1), (9367191466353131596436172679, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_13, prime_oneHundredThreeCW_9367191466353131596436172679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244828 : Nat.totient 121773489062590710753670244828 = 57305171323572099178197762240 := by
  rw [← show ((([(2, 2), (17, 1), (1790786603861628099318680071, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_17, prime_oneHundredThreeCW_1790786603861628099318680071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244829 : Nat.totient 121773489062590710753670244829 = 63258940956222211018216209600 := by
  rw [← show ((([(3, 1), (7, 1), (11, 1), (5463023, 1), (22420523, 1), (4303898311871, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_11, prime_oneHundredThreeCW_5463023, prime_oneHundredThreeCW_22420523, prime_oneHundredThreeCW_4303898311871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244830 : Nat.totient 121773489062590710753670244830 = 48709349601255243838804618752 := by
  rw [← show ((([(2, 1), (5, 1), (1065689, 1), (153740329, 1), (74324921726243, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_1065689, prime_oneHundredThreeCW_153740329, prime_oneHundredThreeCW_74324921726243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244831 : Nat.totient 121773489062590710753670244831 = 121768789043787522075663315840 := by
  rw [← show ((([(25999, 1), (7496729, 1), (624775936065270361, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_25999, prime_oneHundredThreeCW_7496729, prime_oneHundredThreeCW_624775936065270361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244832 : Nat.totient 121773489062590710753670244832 = 40591163020863570251223414912 := by
  rw [← show ((([(2, 5), (3, 1), (1268473844401986570350731717, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_1268473844401986570350731717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244833 : Nat.totient 121773489062590710753670244833 = 117472430636807308253443381248 := by
  rw [← show ((([(29, 1), (1153, 1), (3641878429960544030674709, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_29, prime_oneHundredThreeCW_1153, prime_oneHundredThreeCW_3641878429960544030674709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244834 : Nat.totient 121773489062590710753670244834 = 58239444448993539308829824880 := by
  rw [← show ((([(2, 1), (23, 1), (1157381, 1), (2287275981055704942859, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_23, prime_oneHundredThreeCW_1157381, prime_oneHundredThreeCW_2287275981055704942859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244835 : Nat.totient 121773489062590710753670244835 = 64945860833381712401957463888 := by
  rw [← show ((([(3, 2), (5, 1), (2706077534724238016748227663, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_2706077534724238016748227663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244836 : Nat.totient 121773489062590710753670244836 = 52188636596441568491490678624 := by
  rw [← show ((([(2, 2), (7, 3), (33172709, 1), (2675578511342088707, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_33172709, prime_oneHundredThreeCW_2675578511342088707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244837 : Nat.totient 121773489062590710753670244837 = 121654657016510603298748445920 := by
  rw [← show ((([(1823, 1), (2339, 1), (28558530660924646699721, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_1823, prime_oneHundredThreeCW_2339, prime_oneHundredThreeCW_28558530660924646699721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244838 : Nat.totient 121773489062590710753670244838 = 40591163020863570251223414944 := by
  rw [← show ((([(2, 1), (3, 1), (20295581510431785125611707473, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_20295581510431785125611707473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244839 : Nat.totient 121773489062590710753670244839 = 120247143520552848844239677440 := by
  rw [← show ((([(113, 1), (269, 1), (5837891, 1), (686224223113002257, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_113, prime_oneHundredThreeCW_269, prime_oneHundredThreeCW_5837891, prime_oneHundredThreeCW_686224223113002257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244840 : Nat.totient 121773489062590710753670244840 = 40630256725041781470006988800 := by
  rw [← show ((([(2, 3), (5, 1), (11, 1), (13, 1), (167, 1), (127479470146340930817041, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_11, prime_oneHundredThreeCW_13, prime_oneHundredThreeCW_167, prime_oneHundredThreeCW_127479470146340930817041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244841 : Nat.totient 121773489062590710753670244841 = 81182326038458255897886856080 := by
  rw [← show ((([(3, 1), (24834870941, 1), (1634442277445115967, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_24834870941, prime_oneHundredThreeCW_1634442277445115967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244842 : Nat.totient 121773489062590710753670244842 = 59241146781004112914346016000 := by
  rw [← show ((([(2, 1), (37, 1), (5888633, 1), (279451562023819383001, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_37, prime_oneHundredThreeCW_5888633, prime_oneHundredThreeCW_279451562023819383001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244843 : Nat.totient 121773489062590710753670244843 = 93628709822191847844810931200 := by
  rw [← show ((([(7, 1), (19, 1), (41, 1), (43, 1), (199, 1), (743, 1), (3512423759291137781, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_19, prime_oneHundredThreeCW_41, prime_oneHundredThreeCW_43, prime_oneHundredThreeCW_199, prime_oneHundredThreeCW_743, prime_oneHundredThreeCW_3512423759291137781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244844 : Nat.totient 121773489062590710753670244844 = 40536235871985541062791439360 := by
  rw [← show ((([(2, 2), (3, 2), (739, 1), (4577262406502432369330561, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_739, prime_oneHundredThreeCW_4577262406502432369330561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244845 : Nat.totient 121773489062590710753670244845 = 91569660567397680926594288640 := by
  rw [← show ((([(5, 1), (17, 1), (773, 1), (264360628319, 1), (7010638194811, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_17, prime_oneHundredThreeCW_773, prime_oneHundredThreeCW_264360628319, prime_oneHundredThreeCW_7010638194811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244846 : Nat.totient 121773489062590710753670244846 = 60775274083453454735529184320 := by
  rw [← show ((([(2, 1), (547, 1), (379541, 1), (293276138994231955049, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_547, prime_oneHundredThreeCW_379541, prime_oneHundredThreeCW_293276138994231955049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244847 : Nat.totient 121773489062590710753670244847 = 80833904041548054062522164928 := by
  rw [← show ((([(3, 1), (233, 1), (174211000089543219962332253, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_233, prime_oneHundredThreeCW_174211000089543219962332253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244848 : Nat.totient 121773489062590710753670244848 = 60883772655283463136769432320 := by
  rw [← show ((([(2, 4), (20509, 1), (19676231, 1), (18860203279645757, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_20509, prime_oneHundredThreeCW_19676231, prime_oneHundredThreeCW_18860203279645757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244849 : Nat.totient 121773489062590710753670244849 = 117050929680557799883138176000 := by
  rw [← show ((([(31, 1), (149, 1), (35507, 1), (659353, 1), (1126089271124201, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_31, prime_oneHundredThreeCW_149, prime_oneHundredThreeCW_35507, prime_oneHundredThreeCW_659353, prime_oneHundredThreeCW_1126089271124201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244850 : Nat.totient 121773489062590710753670244850 = 27644465191521402056138342400 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (7, 1), (157, 1), (2269, 1), (9601559269, 1), (33906857041, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_157, prime_oneHundredThreeCW_2269, prime_oneHundredThreeCW_9601559269, prime_oneHundredThreeCW_33906857041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244851 : Nat.totient 121773489062590710753670244851 = 110675265856343493622647281280 := by
  rw [← show ((([(11, 1), (3967, 1), (98731854929, 1), (28264451867287, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_11, prime_oneHundredThreeCW_3967, prime_oneHundredThreeCW_98731854929, prime_oneHundredThreeCW_28264451867287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244852 : Nat.totient 121773489062590710753670244852 = 60875585807057653013191434240 := by
  rw [← show ((([(2, 2), (5927, 1), (68993, 1), (16953193, 1), (4391382787331, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_5927, prime_oneHundredThreeCW_68993, prime_oneHundredThreeCW_16953193, prime_oneHundredThreeCW_4391382787331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244853 : Nat.totient 121773489062590710753670244853 = 74937530207640930244021571328 := by
  rw [← show ((([(3, 3), (13, 1), (49197947, 1), (7051778344985375249, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_13, prime_oneHundredThreeCW_49197947, prime_oneHundredThreeCW_7051778344985375249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244854 : Nat.totient 121773489062590710753670244854 = 60850584721002219141953848320 := by
  rw [← show ((([(2, 1), (2129, 1), (8089, 1), (1623157, 1), (2178169778854231, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_2129, prime_oneHundredThreeCW_8089, prime_oneHundredThreeCW_1623157, prime_oneHundredThreeCW_2178169778854231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244855 : Nat.totient 121773489062590710753670244855 = 97418791247325981816160055808 := by
  rw [← show ((([(5, 1), (35469039883, 1), (686646661224995137, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_35469039883, prime_oneHundredThreeCW_686646661224995137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244856 : Nat.totient 121773489062590710753670244856 = 40546197915899810445564680448 := by
  rw [← show ((([(2, 3), (3, 1), (907, 1), (191353, 1), (29234720457663753239, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_907, prime_oneHundredThreeCW_191353, prime_oneHundredThreeCW_29234720457663753239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244857 : Nat.totient 121773489062590710753670244857 = 99839094855963876532111798080 := by
  rw [← show ((([(7, 1), (23, 1), (2557757, 1), (295711076119789201741, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_23, prime_oneHundredThreeCW_2557757, prime_oneHundredThreeCW_295711076119789201741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244858 : Nat.totient 121773489062590710753670244858 = 60886744530529081077927517084 := by
  rw [← show ((([(2, 1), (79458166523, 1), (766274219449438823, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_79458166523, prime_oneHundredThreeCW_766274219449438823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244859 : Nat.totient 121773489062590710753670244859 = 79280370937296888098295920000 := by
  rw [← show ((([(3, 1), (71, 1), (107, 1), (7541, 1), (398045651, 1), (1780030912739, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_71, prime_oneHundredThreeCW_107, prime_oneHundredThreeCW_7541, prime_oneHundredThreeCW_398045651, prime_oneHundredThreeCW_1780030912739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244860 : Nat.totient 121773489062590710753670244860 = 48639689121074402280132771072 := by
  rw [← show ((([(2, 2), (5, 1), (1283, 1), (1543, 1), (245789, 1), (12513181067307923, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_1283, prime_oneHundredThreeCW_1543, prime_oneHundredThreeCW_245789, prime_oneHundredThreeCW_12513181067307923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244861 : Nat.totient 121773489062590710753670244861 = 120306327921184126138159337712 := by
  rw [← show ((([(83, 1), (11274379, 1), (130131377580408022573, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_83, prime_oneHundredThreeCW_11274379, prime_oneHundredThreeCW_130131377580408022573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244862 : Nat.totient 121773489062590710753670244862 = 31767194544816564837435801600 := by
  rw [← show ((([(2, 1), (3, 2), (11, 2), (17, 2), (19, 1), (29, 1), (43711, 1), (63798727, 1), (125904913, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_11, prime_oneHundredThreeCW_17, prime_oneHundredThreeCW_19, prime_oneHundredThreeCW_29, prime_oneHundredThreeCW_43711, prime_oneHundredThreeCW_63798727, prime_oneHundredThreeCW_125904913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244863 : Nat.totient 121773489062590710753670244863 = 121772631448167476687528858520 := by
  rw [← show ((([(141991, 1), (615281548379, 1), (1393856422667, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_141991, prime_oneHundredThreeCW_615281548379, prime_oneHundredThreeCW_1393856422667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244864 : Nat.totient 121773489062590710753670244864 = 51023014205981550913606533120 := by
  rw [← show ((([(2, 9), (7, 1), (53, 1), (283, 1), (20209425739, 1), (112090413311, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_53, prime_oneHundredThreeCW_283, prime_oneHundredThreeCW_20209425739, prime_oneHundredThreeCW_112090413311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244865 : Nat.totient 121773489062590710753670244865 = 63447862915052948841424920576 := by
  rw [← show ((([(3, 1), (5, 1), (67, 1), (139, 1), (929, 1), (2709877, 1), (346263404496979, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_67, prime_oneHundredThreeCW_139, prime_oneHundredThreeCW_929, prime_oneHundredThreeCW_2709877, prime_oneHundredThreeCW_346263404496979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244866 : Nat.totient 121773489062590710753670244866 = 56187665744437772979478894080 := by
  rw [← show ((([(2, 1), (13, 1), (3631, 1), (18547817, 1), (43481797, 1), (1599384439, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_13, prime_oneHundredThreeCW_3631, prime_oneHundredThreeCW_18547817, prime_oneHundredThreeCW_43481797, prime_oneHundredThreeCW_1599384439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244867 : Nat.totient 121773489062590710753670244867 = 121763946571251493861054859520 := by
  rw [← show ((([(13931, 1), (152239, 1), (82440737, 1), (696470408999, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_13931, prime_oneHundredThreeCW_152239, prime_oneHundredThreeCW_82440737, prime_oneHundredThreeCW_696470408999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244868 : Nat.totient 121773489062590710753670244868 = 40591163020579668694854000960 := by
  rw [← show ((([(2, 2), (3, 1), (142976478569, 1), (70975246115874931, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_142976478569, prime_oneHundredThreeCW_70975246115874931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244869 : Nat.totient 121773489062590710753670244869 = 121773249594708491298448468096 := by
  rw [← show ((([(508517, 1), (239467882219455221268257, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_508517, prime_oneHundredThreeCW_239467882219455221268257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244870 : Nat.totient 121773489062590710753670244870 = 46865008123860734852417750400 := by
  rw [← show ((([(2, 1), (5, 1), (47, 1), (59, 1), (1501394158519, 1), (2924880709901, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_47, prime_oneHundredThreeCW_59, prime_oneHundredThreeCW_1501394158519, prime_oneHundredThreeCW_2924880709901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244871 : Nat.totient 121773489062590710753670244871 = 69175082182147449868883672640 := by
  rw [← show ((([(3, 2), (7, 1), (191, 1), (1523, 1), (6644754341984946887069, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_191, prime_oneHundredThreeCW_1523, prime_oneHundredThreeCW_6644754341984946887069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244872 : Nat.totient 121773489062590710753670244872 = 60884066241051830102968958976 := by
  rw [← show ((([(2, 3), (26717, 1), (170369, 1), (1450637, 1), (2305290961609, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_26717, prime_oneHundredThreeCW_170369, prime_oneHundredThreeCW_1450637, prime_oneHundredThreeCW_2305290961609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244873 : Nat.totient 121773489062590710753670244873 = 108019636994542432769013381120 := by
  rw [← show ((([(11, 1), (79, 1), (89, 1), (1997, 1), (788433196481412948049, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_11, prime_oneHundredThreeCW_79, prime_oneHundredThreeCW_89, prime_oneHundredThreeCW_1997, prime_oneHundredThreeCW_788433196481412948049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244874 : Nat.totient 121773489062590710753670244874 = 40591163020858685759354691168 := by
  rw [← show ((([(2, 1), (3, 1), (8338683201983, 1), (2433907251159913, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_8338683201983, prime_oneHundredThreeCW_2433907251159913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244875 : Nat.totient 121773489062590710753670244875 = 97418791250072568602936195800 := by
  rw [← show ((([(5, 3), (974187912500725686029361959, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_974187912500725686029361959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244876 : Nat.totient 121773489062590710753670244876 = 59888601178323300370657497360 := by
  rw [← show ((([(2, 2), (61, 1), (499071676486027503088812479, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_61, prime_oneHundredThreeCW_499071676486027503088812479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244877 : Nat.totient 121773489062590710753670244877 = 79758932109322714004059407360 := by
  rw [← show ((([(3, 1), (97, 1), (137, 1), (3054493417176880897827031, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_97, prime_oneHundredThreeCW_137, prime_oneHundredThreeCW_3054493417176880897827031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244878 : Nat.totient 121773489062590710753670244878 = 52024005145848229694926563552 := by
  rw [← show ((([(2, 1), (7, 1), (317, 1), (542745347, 1), (50555608595593223, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_317, prime_oneHundredThreeCW_542745347, prime_oneHundredThreeCW_50555608595593223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244879 : Nat.totient 121773489062590710753670244879 = 101524793296953184724927692800 := by
  rw [← show ((([(13, 1), (17, 1), (37, 2), (73, 1), (116267101, 1), (47421722388727, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_13, prime_oneHundredThreeCW_17, prime_oneHundredThreeCW_37, prime_oneHundredThreeCW_73, prime_oneHundredThreeCW_116267101, prime_oneHundredThreeCW_47421722388727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244880 : Nat.totient 121773489062590710753670244880 = 30059086695810874965825408000 := by
  rw [← show ((([(2, 4), (3, 3), (5, 1), (23, 2), (31, 1), (4073851, 1), (843871834478107, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_23, prime_oneHundredThreeCW_31, prime_oneHundredThreeCW_4073851, prime_oneHundredThreeCW_843871834478107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244881 : Nat.totient 121773489062590710753670244881 = 115364255292777645750758269248 := by
  rw [← show ((([(19, 1), (1122587, 1), (5709251045392693781777, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_19, prime_oneHundredThreeCW_1122587, prime_oneHundredThreeCW_5709251045392693781777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244882 : Nat.totient 121773489062590710753670244882 = 60886720766640956318919856512 := by
  rw [← show ((([(2, 1), (2698453, 1), (50693309, 1), (445099652402633, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_2698453, prime_oneHundredThreeCW_50693309, prime_oneHundredThreeCW_445099652402633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244883 : Nat.totient 121773489062590710753670244883 = 81181328359709929316757008160 := by
  rw [← show ((([(3, 1), (81371, 1), (118355048719, 1), (4214781383789, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_81371, prime_oneHundredThreeCW_118355048719, prime_oneHundredThreeCW_4214781383789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244884 : Nat.totient 121773489062590710753670244884 = 54001547256137787473911416000 := by
  rw [← show ((([(2, 2), (11, 1), (41, 1), (67501934070172234342389271, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_11, prime_oneHundredThreeCW_41, prime_oneHundredThreeCW_67501934070172234342389271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244885 : Nat.totient 121773489062590710753670244885 = 83427571330671682518498017280 := by
  rw [← show ((([(5, 1), (7, 2), (1933, 1), (2689, 1), (5695721, 1), (16788631681949, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_1933, prime_oneHundredThreeCW_2689, prime_oneHundredThreeCW_5695721, prime_oneHundredThreeCW_16788631681949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244886 : Nat.totient 121773489062590710753670244886 = 39633324679662600152629403040 := by
  rw [← show ((([(2, 1), (3, 1), (43, 1), (2861, 1), (164973878952974526109847, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_43, prime_oneHundredThreeCW_2861, prime_oneHundredThreeCW_164973878952974526109847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244887 : Nat.totient 121773489062590710753670244887 = 121739784803232119358499006776 := by
  rw [← show ((([(3613, 1), (33704259358591395171234499, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3613, prime_oneHundredThreeCW_33704259358591395171234499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244888 : Nat.totient 121773489062590710753670244888 = 60848087661994745936337004800 := by
  rw [← show ((([(2, 3), (2281, 1), (5087, 1), (2470218071, 1), (531056153203, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_2281, prime_oneHundredThreeCW_5087, prime_oneHundredThreeCW_2470218071, prime_oneHundredThreeCW_531056153203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244889 : Nat.totient 121773489062590710753670244889 = 80380806213282106903599513600 := by
  rw [← show ((([(3, 2), (103, 1), (6151, 1), (389297, 1), (1230337, 1), (44588426513, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_103, prime_oneHundredThreeCW_6151, prime_oneHundredThreeCW_389297, prime_oneHundredThreeCW_1230337, prime_oneHundredThreeCW_44588426513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244890 : Nat.totient 121773489062590710753670244890 = 48709394889514985908102607424 := by
  rw [← show ((([(2, 1), (5, 1), (66224317, 1), (183880324598275148317, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_66224317, prime_oneHundredThreeCW_183880324598275148317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244891 : Nat.totient 121773489062590710753670244891 = 117567864536901203030220160000 := by
  rw [← show ((([(29, 1), (19421, 1), (285533, 1), (1611353, 1), (469933237751, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_29, prime_oneHundredThreeCW_19421, prime_oneHundredThreeCW_285533, prime_oneHundredThreeCW_1611353, prime_oneHundredThreeCW_469933237751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244892 : Nat.totient 121773489062590710753670244892 = 32080034831368110103454929920 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (13, 1), (1021, 1), (6983, 1), (15640921168598703557, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_13, prime_oneHundredThreeCW_1021, prime_oneHundredThreeCW_6983, prime_oneHundredThreeCW_15640921168598703557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244893 : Nat.totient 121773489062590710753670244893 = 120525009946778820678514941312 := by
  rw [← show ((([(109, 1), (919, 1), (427477097, 1), (2843792397755039, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_109, prime_oneHundredThreeCW_919, prime_oneHundredThreeCW_427477097, prime_oneHundredThreeCW_2843792397755039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244894 : Nat.totient 121773489062590710753670244894 = 60662070183093321373857194400 := by
  rw [← show ((([(2, 1), (271, 1), (4290646421, 1), (52363749425769917, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_271, prime_oneHundredThreeCW_4290646421, prime_oneHundredThreeCW_52363749425769917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244895 : Nat.totient 121773489062590710753670244895 = 59041691666710647638143148960 := by
  rw [← show ((([(3, 1), (5, 1), (11, 1), (738021145833883095476789363, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_11, prime_oneHundredThreeCW_738021145833883095476789363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244896 : Nat.totient 121773489062590710753670244896 = 57303492547142220596706201600 := by
  rw [← show ((([(2, 5), (17, 1), (34141, 1), (196925579, 1), (33294728768831, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_17, prime_oneHundredThreeCW_34141, prime_oneHundredThreeCW_196925579, prime_oneHundredThreeCW_33294728768831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244897 : Nat.totient 121773489062590710753670244897 = 121773489062590710753670244896 := by
  rw [← show ((([(121773489062590710753670244897, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_121773489062590710753670244897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244898 : Nat.totient 121773489062590710753670244898 = 40591163020863570251223414960 := by
  rw [← show ((([(2, 1), (3, 2), (6765193836810595041870569161, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_6765193836810595041870569161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244899 : Nat.totient 121773489062590710753670244899 = 104368056546382337178559158720 := by
  rw [← show ((([(7, 1), (11321, 1), (1536632163521530288259117, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_7, prime_oneHundredThreeCW_11321, prime_oneHundredThreeCW_1536632163521530288259117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244900 : Nat.totient 121773489062590710753670244900 = 46138267807677159793970163840 := by
  rw [← show ((([(2, 2), (5, 2), (19, 1), (6173, 1), (10382522279757407961127, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_5, prime_oneHundredThreeCW_19, prime_oneHundredThreeCW_6173, prime_oneHundredThreeCW_10382522279757407961127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244901 : Nat.totient 121773489062590710753670244901 = 80970361252977976052518063104 := by
  rw [← show ((([(3, 1), (383, 1), (164912417, 1), (642657180141501097, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_3, prime_oneHundredThreeCW_383, prime_oneHundredThreeCW_164912417, prime_oneHundredThreeCW_642657180141501097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThreeCW_121773489062590710753670244902 : Nat.totient 121773489062590710753670244902 = 60878668225520558944684725600 := by
  rw [← show ((([(2, 1), (7727, 1), (314747, 1), (19357451, 1), (1293308327029, 1)] : List FactorBlock).map factorBlockValue).prod) = 121773489062590710753670244902 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThreeCW_2, prime_oneHundredThreeCW_7727, prime_oneHundredThreeCW_314747, prime_oneHundredThreeCW_19357451, prime_oneHundredThreeCW_1293308327029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThreeCW : certifiedKill 2 121773489062590710753670244799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThreeCW_121773489062590710753670244800, phi_oneHundredThreeCW_121773489062590710753670244801, phi_oneHundredThreeCW_121773489062590710753670244802,
    phi_oneHundredThreeCW_121773489062590710753670244803, phi_oneHundredThreeCW_121773489062590710753670244804, phi_oneHundredThreeCW_121773489062590710753670244805,
    phi_oneHundredThreeCW_121773489062590710753670244806, phi_oneHundredThreeCW_121773489062590710753670244807, phi_oneHundredThreeCW_121773489062590710753670244808,
    phi_oneHundredThreeCW_121773489062590710753670244809, phi_oneHundredThreeCW_121773489062590710753670244810, phi_oneHundredThreeCW_121773489062590710753670244811,
    phi_oneHundredThreeCW_121773489062590710753670244812, phi_oneHundredThreeCW_121773489062590710753670244813, phi_oneHundredThreeCW_121773489062590710753670244814,
    phi_oneHundredThreeCW_121773489062590710753670244815, phi_oneHundredThreeCW_121773489062590710753670244816, phi_oneHundredThreeCW_121773489062590710753670244817,
    phi_oneHundredThreeCW_121773489062590710753670244818, phi_oneHundredThreeCW_121773489062590710753670244819, phi_oneHundredThreeCW_121773489062590710753670244820,
    phi_oneHundredThreeCW_121773489062590710753670244821, phi_oneHundredThreeCW_121773489062590710753670244822, phi_oneHundredThreeCW_121773489062590710753670244823,
    phi_oneHundredThreeCW_121773489062590710753670244824, phi_oneHundredThreeCW_121773489062590710753670244825, phi_oneHundredThreeCW_121773489062590710753670244826,
    phi_oneHundredThreeCW_121773489062590710753670244827, phi_oneHundredThreeCW_121773489062590710753670244828, phi_oneHundredThreeCW_121773489062590710753670244829,
    phi_oneHundredThreeCW_121773489062590710753670244830, phi_oneHundredThreeCW_121773489062590710753670244831, phi_oneHundredThreeCW_121773489062590710753670244832,
    phi_oneHundredThreeCW_121773489062590710753670244833, phi_oneHundredThreeCW_121773489062590710753670244834, phi_oneHundredThreeCW_121773489062590710753670244835,
    phi_oneHundredThreeCW_121773489062590710753670244836, phi_oneHundredThreeCW_121773489062590710753670244837, phi_oneHundredThreeCW_121773489062590710753670244838,
    phi_oneHundredThreeCW_121773489062590710753670244839, phi_oneHundredThreeCW_121773489062590710753670244840, phi_oneHundredThreeCW_121773489062590710753670244841,
    phi_oneHundredThreeCW_121773489062590710753670244842, phi_oneHundredThreeCW_121773489062590710753670244843, phi_oneHundredThreeCW_121773489062590710753670244844,
    phi_oneHundredThreeCW_121773489062590710753670244845, phi_oneHundredThreeCW_121773489062590710753670244846, phi_oneHundredThreeCW_121773489062590710753670244847,
    phi_oneHundredThreeCW_121773489062590710753670244848, phi_oneHundredThreeCW_121773489062590710753670244849, phi_oneHundredThreeCW_121773489062590710753670244850,
    phi_oneHundredThreeCW_121773489062590710753670244851, phi_oneHundredThreeCW_121773489062590710753670244852, phi_oneHundredThreeCW_121773489062590710753670244853,
    phi_oneHundredThreeCW_121773489062590710753670244854, phi_oneHundredThreeCW_121773489062590710753670244855, phi_oneHundredThreeCW_121773489062590710753670244856,
    phi_oneHundredThreeCW_121773489062590710753670244857, phi_oneHundredThreeCW_121773489062590710753670244858, phi_oneHundredThreeCW_121773489062590710753670244859,
    phi_oneHundredThreeCW_121773489062590710753670244860, phi_oneHundredThreeCW_121773489062590710753670244861, phi_oneHundredThreeCW_121773489062590710753670244862,
    phi_oneHundredThreeCW_121773489062590710753670244863, phi_oneHundredThreeCW_121773489062590710753670244864, phi_oneHundredThreeCW_121773489062590710753670244865,
    phi_oneHundredThreeCW_121773489062590710753670244866, phi_oneHundredThreeCW_121773489062590710753670244867, phi_oneHundredThreeCW_121773489062590710753670244868,
    phi_oneHundredThreeCW_121773489062590710753670244869, phi_oneHundredThreeCW_121773489062590710753670244870, phi_oneHundredThreeCW_121773489062590710753670244871,
    phi_oneHundredThreeCW_121773489062590710753670244872, phi_oneHundredThreeCW_121773489062590710753670244873, phi_oneHundredThreeCW_121773489062590710753670244874,
    phi_oneHundredThreeCW_121773489062590710753670244875, phi_oneHundredThreeCW_121773489062590710753670244876, phi_oneHundredThreeCW_121773489062590710753670244877,
    phi_oneHundredThreeCW_121773489062590710753670244878, phi_oneHundredThreeCW_121773489062590710753670244879, phi_oneHundredThreeCW_121773489062590710753670244880,
    phi_oneHundredThreeCW_121773489062590710753670244881, phi_oneHundredThreeCW_121773489062590710753670244882, phi_oneHundredThreeCW_121773489062590710753670244883,
    phi_oneHundredThreeCW_121773489062590710753670244884, phi_oneHundredThreeCW_121773489062590710753670244885, phi_oneHundredThreeCW_121773489062590710753670244886,
    phi_oneHundredThreeCW_121773489062590710753670244887, phi_oneHundredThreeCW_121773489062590710753670244888, phi_oneHundredThreeCW_121773489062590710753670244889,
    phi_oneHundredThreeCW_121773489062590710753670244890, phi_oneHundredThreeCW_121773489062590710753670244891, phi_oneHundredThreeCW_121773489062590710753670244892,
    phi_oneHundredThreeCW_121773489062590710753670244893, phi_oneHundredThreeCW_121773489062590710753670244894, phi_oneHundredThreeCW_121773489062590710753670244895,
    phi_oneHundredThreeCW_121773489062590710753670244896, phi_oneHundredThreeCW_121773489062590710753670244897, phi_oneHundredThreeCW_121773489062590710753670244898,
    phi_oneHundredThreeCW_121773489062590710753670244899, phi_oneHundredThreeCW_121773489062590710753670244900, phi_oneHundredThreeCW_121773489062590710753670244901,
    phi_oneHundredThreeCW_121773489062590710753670244902
    ]

end TotientTailPeriodKiller
end Erdos249257
